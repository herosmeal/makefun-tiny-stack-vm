// Tiny stack VM implementing the make.fun tiny-stack ISA v1 exactly:
// every instance under the input dir is run and answered with its output
// bytes and its exit code (a trap's own code when it traps).
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const inputRoot = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputRoot = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per-opcode facts keyed by byte: [immediateBytes, popped, pushed].
// A byte missing here is an unknown opcode and traps 5.
const META = new Map([
  [0, [0, 0, 0]], [1, [1, 0, 1]], [2, [4, 0, 1]], [3, [0, 1, 0]],
  [4, [0, 1, 2]], [5, [0, 2, 2]], [6, [0, 2, 3]], [7, [0, 3, 3]],
  [16, [0, 2, 1]], [17, [0, 2, 1]], [18, [0, 2, 1]], [19, [0, 2, 1]],
  [20, [0, 2, 1]], [21, [0, 2, 1]], [22, [0, 2, 1]], [23, [0, 1, 1]],
  [24, [0, 2, 1]], [25, [0, 2, 1]], [26, [0, 2, 1]], [27, [0, 1, 1]],
  [28, [0, 2, 1]], [29, [0, 2, 1]], [30, [0, 2, 1]], [32, [0, 2, 1]],
  [33, [0, 2, 1]], [34, [0, 2, 1]], [48, [2, 0, 0]], [49, [2, 1, 0]],
  [50, [2, 1, 0]], [51, [2, 0, 0]], [52, [0, 0, 0]], [64, [0, 1, 1]],
  [65, [0, 2, 0]], [80, [0, 1, 0]], [81, [0, 1, 0]], [82, [0, 0, 1]],
  [83, [0, 1, 0]],
]);
const encoder = new TextEncoder();

function execute(prog, inp) {
  const n = prog.length;
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const outBuf = new Uint8Array(65536);
  let sp = 0, csp = 0, outLen = 0, inPos = 0, pc = 0, steps = 0;
  const finish = (code) => ({ bytes: outBuf.slice(0, outLen), code });
  for (;;) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const meta = META.get(op);
    if (meta === undefined) return finish(5);
    if (pc + meta[0] >= n) return finish(9);
    steps += 1;
    const next = pc + 1 + meta[0];
    if (sp < meta[1]) return finish(2);
    if (sp - meta[1] + meta[2] > 256) return finish(3);
    pc = next;
    if (op === 0) return finish(0);
    if (op === 1) stack[sp++] = (prog[next - 1] << 24) >> 24;
    else if (op === 2) stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
    else if (op === 3) sp -= 1;
    else if (op === 4) { stack[sp] = stack[sp - 1]; sp += 1; }
    else if (op === 5) { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; }
    else if (op === 6) { stack[sp] = stack[sp - 2]; sp += 1; }
    else if (op === 7) {
      const a = stack[sp - 3];
      stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
    } else if (op === 23) stack[sp - 1] = (-stack[sp - 1]) | 0;
    else if (op === 27) stack[sp - 1] = ~stack[sp - 1];
    else if (op >= 16 && op <= 34 && op !== 23) {
      const b = stack[sp - 1], a = stack[sp - 2];
      let r;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 1; stack[sp - 1] = r;
    } else if (op === 48 || op === 49 || op === 50) {
      const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
      let jump = true;
      if (op !== 48) { const v = stack[--sp]; jump = op === 49 ? v === 0 : v !== 0; }
      if (jump) pc = next + rel;
    } else if (op === 51) {
      if (csp === 64) return finish(7);
      calls[csp++] = next;
      pc = prog[next - 2] | (prog[next - 1] << 8);
    } else if (op === 52) {
      if (csp === 0) return finish(8);
      pc = calls[--csp];
    } else if (op === 64) {
      const addr = stack[sp - 1];
      if (addr < 0 || addr > 255) return finish(6);
      stack[sp - 1] = mem[addr];
    } else if (op === 65) {
      const addr = stack[sp - 1];
      if (addr < 0 || addr > 255) return finish(6);
      mem[addr] = stack[sp - 2]; sp -= 2;
    } else if (op === 80) {
      const text = encoder.encode(String(stack[sp - 1]));
      if (outLen + text.length > 65536) return finish(11);
      sp -= 1; outBuf.set(text, outLen); outLen += text.length;
    } else if (op === 81) {
      if (outLen + 1 > 65536) return finish(11);
      outBuf[outLen++] = stack[--sp] & 255;
    } else if (op === 82) stack[sp++] = inPos < inp.length ? inp[inPos++] : -1;
    else if (op === 83) return finish(stack[--sp] & 255);
  }
}

for (const id of readdirSync(inputRoot).sort()) {
  const dir = join(outputRoot, id);
  mkdirSync(dir, { recursive: true });
  let result;
  try {
    const prog = readFileSync(join(inputRoot, id, 'program.bin'));
    let inp;
    try { inp = readFileSync(join(inputRoot, id, 'input.bin')); }
    catch { inp = new Uint8Array(0); }
    result = execute(prog, inp);
  } catch { result = { bytes: new Uint8Array(0), code: 0 }; }
  writeFileSync(join(dir, 'stdout.bin'), result.bytes);
  writeFileSync(join(dir, 'exit.txt'), String(result.code) + '\n');
}
