// news-image-20261122 — entry 2: broadsheet courier.
//
// The entry artwork is the pinned PNG drawn for Sunday 22 November 2026
// ("THE WORLD IN ONE DAY", 36 verified stories). This program audits that
// PNG beside it — signature, chunk CRCs, exactly one 1024x1024 IHDR header,
// no chunk after IEND, pinned sha256, one full inflate of the pixel stream
// — and then copies its exact bytes to the grader output directory.
// Deterministic: repeated runs emit identical bytes, and the output is
// byte-for-byte the audited input.

import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { inflateSync } from "node:zlib";
import { fileURLToPath } from "node:url";

const PINNED_SHA256 =
  "ddffa306a225e720ab0bbd4a4a17539b766fa30c7dedcfd953f7b6002b78ecea";
const EXPECTED_WIDTH = 1024;
const EXPECTED_HEIGHT = 1024;
const EXPECTED_BIT_DEPTH = 8;
const EXPECTED_COLOR_TYPE = 2;
const PNG_SIGNATURE = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
const PNG_CHUNK_HEADER = 8;
const PNG_CHUNK_OVERHEAD = 12;
const RGB_CHANNELS = 3;

function buildCrcTable(): Uint32Array {
  const tableOutcome = new Uint32Array(256);
  for (let index = 0; index < 256; index += 1) {
    let remainder = index;
    for (let round = 0; round < 8; round += 1) {
      const lowBitSet = (remainder & 1) !== 0;
      remainder = lowBitSet ? (remainder >>> 1) ^ 0xedb88320 : remainder >>> 1;
    }
    tableOutcome[index] = remainder >>> 0;
  }
  return tableOutcome;
}

const CRC_TABLE = buildCrcTable();

function crc32Over(payload: Buffer): number {
  let running = 0xffffffff;
  for (let index = 0; index < payload.length; index += 1) {
    const tableSlot = (running ^ payload[index]) & 0xff;
    running = (running >>> 8) ^ CRC_TABLE[tableSlot];
  }
  const digestOutcome = (running ^ 0xffffffff) >>> 0;
  return digestOutcome;
}

function sha256Hex(payload: Buffer): string {
  const hashOutcome = createHash("sha256").update(payload).digest("hex");
  return hashOutcome;
}

function failWith(message: string): never {
  throw new Error(message);
}

function resolveSourcePath(): string {
  const modulePath = fileURLToPath(import.meta.url);
  const folderPath = modulePath.slice(0, modulePath.lastIndexOf("/"));
  const sourceOutcome = join(folderPath, "entry.png");
  return sourceOutcome;
}

function resolveOutputDir(): string {
  const override = process.env.MAKEFUN_OUTPUT_DIR;
  const dirOutcome = override !== undefined && override !== ""
    ? resolve(override)
    : "/output";
  return dirOutcome;
}

function verifySignature(broadsheetBytes: Buffer): void {
  for (let index = 0; index < PNG_SIGNATURE.length; index += 1) {
    const byteMatches = broadsheetBytes[index] === PNG_SIGNATURE[index];
    if (byteMatches === false) {
      failWith("audit failed: PNG signature mismatch at byte " + String(index));
    }
  }
}

type ChunkLedger = {
  chunkCount: number;
  ihdrSeen: number;
  ihdrWidth: number;
  ihdrHeight: number;
  ihdrBitDepth: number;
  ihdrColorType: number;
  idatParts: Buffer[];
  idatBytes: number;
  sawIend: boolean;
};

function parseChunkLedger(broadsheetBytes: Buffer): ChunkLedger {
  const ledgerOutcome: ChunkLedger = {
    chunkCount: 0,
    ihdrSeen: 0,
    ihdrWidth: 0,
    ihdrHeight: 0,
    ihdrBitDepth: 0,
    ihdrColorType: 0,
    idatParts: [],
    idatBytes: 0,
    sawIend: false,
  };
  let walkOffset = PNG_CHUNK_HEADER;
  let leadChunk = true;
  while (walkOffset + PNG_CHUNK_OVERHEAD <= broadsheetBytes.length) {
    const dataLength = broadsheetBytes.readUInt32BE(walkOffset);
    const typeLabel = broadsheetBytes
      .subarray(walkOffset + 4, walkOffset + 8)
      .toString("ascii");
    const dataStart = walkOffset + 8;
    const dataEnd = dataStart + dataLength;
    const chunkEnd = dataEnd + 4;
    if (chunkEnd > broadsheetBytes.length) {
      failWith("audit failed: chunk " + typeLabel + " overruns file");
    }
    if (ledgerOutcome.sawIend === true) {
      failWith("audit failed: chunk " + typeLabel + " after IEND");
    }
    const storedCrc = broadsheetBytes.readUInt32BE(dataEnd);
    const crcScope = Buffer.concat([
      broadsheetBytes.subarray(walkOffset + 4, walkOffset + 8),
      broadsheetBytes.subarray(dataStart, dataEnd),
    ]);
    const computedCrc = crc32Over(crcScope);
    if (computedCrc !== storedCrc) {
      failWith("audit failed: CRC mismatch in chunk " + typeLabel);
    }
    if (leadChunk === true && typeLabel !== "IHDR") {
      failWith("audit failed: first chunk is " + typeLabel + ", not IHDR");
    }
    leadChunk = false;
    ledgerOutcome.chunkCount += 1;
    if (typeLabel === "IHDR") {
      ledgerOutcome.ihdrSeen += 1;
      ledgerOutcome.ihdrWidth = broadsheetBytes.readUInt32BE(dataStart);
      ledgerOutcome.ihdrHeight = broadsheetBytes.readUInt32BE(dataStart + 4);
      ledgerOutcome.ihdrBitDepth = broadsheetBytes[dataStart + 8];
      ledgerOutcome.ihdrColorType = broadsheetBytes[dataStart + 9];
    }
    if (typeLabel === "IDAT") {
      ledgerOutcome.idatParts.push(
        broadsheetBytes.subarray(dataStart, dataEnd),
      );
      ledgerOutcome.idatBytes += dataLength;
    }
    if (typeLabel === "IEND") {
      ledgerOutcome.sawIend = true;
    }
    walkOffset = chunkEnd;
  }
  if (walkOffset !== broadsheetBytes.length) {
    failWith("audit failed: trailing bytes after last chunk");
  }
  if (ledgerOutcome.sawIend === false) {
    failWith("audit failed: missing IEND chunk");
  }
  if (ledgerOutcome.ihdrSeen !== 1) {
    failWith("audit failed: IHDR seen " + String(ledgerOutcome.ihdrSeen));
  }
  return ledgerOutcome;
}

function verifyHeader(ledgerOutcome: ChunkLedger): void {
  if (ledgerOutcome.ihdrWidth !== EXPECTED_WIDTH) {
    failWith("audit failed: width " + String(ledgerOutcome.ihdrWidth));
  }
  if (ledgerOutcome.ihdrHeight !== EXPECTED_HEIGHT) {
    failWith("audit failed: height " + String(ledgerOutcome.ihdrHeight));
  }
  if (ledgerOutcome.ihdrBitDepth !== EXPECTED_BIT_DEPTH) {
    failWith("audit failed: bit depth " + String(ledgerOutcome.ihdrBitDepth));
  }
  if (ledgerOutcome.ihdrColorType !== EXPECTED_COLOR_TYPE) {
    failWith("audit failed: color type " + String(ledgerOutcome.ihdrColorType));
  }
  if (ledgerOutcome.idatParts.length === 0) {
    failWith("audit failed: no IDAT pixel data");
  }
}

function paethPredictor(left: number, above: number, aboveLeft: number): number {
  const estimate = left + above - aboveLeft;
  const distLeft = Math.abs(estimate - left);
  const distAbove = Math.abs(estimate - above);
  const distAboveLeft = Math.abs(estimate - aboveLeft);
  let picked = left;
  if (distAbove < distLeft && distAbove < distAboveLeft) {
    picked = above;
  }
  if (distAboveLeft < distLeft && distAboveLeft < distAbove) {
    picked = aboveLeft;
  }
  return picked;
}

function inflatePixelStream(ledgerOutcome: ChunkLedger): number {
  const compressed = Buffer.concat(ledgerOutcome.idatParts);
  const inflated = inflateSync(compressed);
  const stride = 1 + EXPECTED_WIDTH * RGB_CHANNELS;
  const expectedLength = EXPECTED_HEIGHT * stride;
  if (inflated.length !== expectedLength) {
    failWith("audit failed: inflated length " + String(inflated.length));
  }
  let checksum = 0;
  let previousRow = Buffer.alloc(EXPECTED_WIDTH * RGB_CHANNELS, 0);
  for (let row = 0; row < EXPECTED_HEIGHT; row += 1) {
    const rowStart = row * stride;
    const filterKind = inflated[rowStart];
    const currentRow = Buffer.alloc(EXPECTED_WIDTH * RGB_CHANNELS, 0);
    for (let col = 0; col < EXPECTED_WIDTH * RGB_CHANNELS; col += 1) {
      const rawValue = inflated[rowStart + 1 + col];
      const leftValue = col >= RGB_CHANNELS ? currentRow[col - RGB_CHANNELS] : 0;
      const aboveValue = previousRow[col];
      const aboveLeftValue =
        col >= RGB_CHANNELS ? previousRow[col - RGB_CHANNELS] : 0;
      let rebuilt = rawValue;
      if (filterKind === 1) {
        rebuilt = (rawValue + leftValue) & 0xff;
      }
      if (filterKind === 2) {
        rebuilt = (rawValue + aboveValue) & 0xff;
      }
      if (filterKind === 3) {
        rebuilt = (rawValue + ((leftValue + aboveValue) >> 1)) & 0xff;
      }
      if (filterKind === 4) {
        rebuilt =
          (rawValue + paethPredictor(leftValue, aboveValue, aboveLeftValue)) &
          0xff;
      }
      if (filterKind > 4) {
        failWith("audit failed: unknown filter " + String(filterKind));
      }
      currentRow[col] = rebuilt;
      checksum = (checksum + rebuilt) >>> 0;
    }
    previousRow = currentRow;
  }
  return checksum;
}

function runCourier(): number {
  const sourcePath = resolveSourcePath();
  const sourcePresent = existsSync(sourcePath);
  if (sourcePresent === false) {
    failWith("audit failed: entry.png missing beside main.ts");
  }
  const broadsheetBytes = readFileSync(sourcePath);
  console.log("audit: file " + String(broadsheetBytes.length) + " bytes");
  verifySignature(broadsheetBytes);
  console.log("audit: PNG signature ok");
  const ledgerOutcome = parseChunkLedger(broadsheetBytes);
  console.log(
    "audit: " + String(ledgerOutcome.chunkCount) + " chunks, CRC ok, " +
      String(ledgerOutcome.idatBytes) + " IDAT bytes",
  );
  verifyHeader(ledgerOutcome);
  console.log("audit: exactly one IHDR 1024x1024 rgb8 ok, IEND last");
  const sealDigest = sha256Hex(broadsheetBytes);
  if (sealDigest !== PINNED_SHA256) {
    failWith("audit failed: sha256 " + sealDigest + " != pinned digest");
  }
  console.log("audit: sha256 pinned digest ok");
  const pixelChecksum = inflatePixelStream(ledgerOutcome);
  console.log(
    "audit: pixels inflated, checksum " + String(pixelChecksum),
  );
  const outputDir = resolveOutputDir();
  mkdirSync(outputDir, { recursive: true });
  const targetPath = join(outputDir, "entry.png");
  writeFileSync(targetPath, broadsheetBytes);
  const writtenBytes = readFileSync(targetPath);
  const writtenDigest = sha256Hex(writtenBytes);
  if (writtenDigest !== PINNED_SHA256) {
    failWith("audit failed: written bytes digest mismatch");
  }
  console.log(
    "courier: wrote " + targetPath + " (" + String(writtenBytes.length) +
      " bytes, sha256 " + writtenDigest + ")",
  );
  const exitOutcome = 0;
  return exitOutcome;
}

try { const exitOutcome = runCourier();
  process.exitCode = exitOutcome;
} catch (caughtError) {
  const reasonText =
    caughtError instanceof Error ? caughtError.message : String(caughtError);
  console.error("courier failed: " + reasonText);
  process.exitCode = 1;
}
