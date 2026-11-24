// stackvm — a complete, exact interpreter for make.fun's tiny stack ISA (kit: generator/subject/ISA.md), built
// by an AI agent for @dinaloripek's entry to the "Build a tiny stack virtual machine" bounty. Where the house
// plain-vm skips the rules ISA.md lists as hard, this one follows the reference semantics to the letter: wrapping
// multiplication (Math.imul, never a float product), unsigned DIVU/MODU/LTU, shift counts masked to 5 bits, PUSH8
// sign extension, EXIT's low byte, IN reading -1 past the end, and every trap with its own exit code (2-11).
// One run answers all 40 instances of a set: /input/<id>/program.bin + input.bin in, stdout.bin + exit.txt out.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables: immediate length (-1: not an opcode), values popped, values pushed. A step checks, in
// ISA.md's order: step limit, pc in bounds, opcode known, immediate fits, underflow (2), overflow (3).
const IM = new Int8Array(256).fill(-1);
const PP = new Int8Array(256);
const PS = new Int8Array(256);
const def = (o: number, im: number, pp: number, ps: number): void => { IM[o] = im; PP[o] = pp; PS[o] = ps; };
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); def(0x03, 0, 1, 0); def(0x17, 0, 1, 1); def(0x1b, 0, 1, 1);
def(0x04, 0, 1, 2); def(0x05, 0, 2, 2); def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
for (let o = 0x10; o <= 0x22; o++) if (o !== 0x17 && o !== 0x1b && o !== 0x1f) def(o, 0, 2, 1);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0); def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0); def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

// Runs one program on its input; a thrown number is a trap's exit code.
function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });
  try {
    for (;;) {
      if (steps === 1000000) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = p[pc];
      const im = IM[op];
      if (im < 0) throw 5;
      if (pc + im >= n) throw 9;
      steps++;
      if (sp < PP[op]) throw 2;
      if (sp - PP[op] + PS[op] > 256) throw 3;
      const nx = pc + 1 + im;
      pc = nx;
      switch (op) {
        case 0x00: return done(0);
        case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
        case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
        case 0x03: sp--; break;
        case 0x04: D[sp] = D[sp - 1]; sp++; break;
        case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
        case 0x06: D[sp] = D[sp - 2]; sp++; break;
        case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
        case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
        case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
        case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
        case 0x20: case 0x21: case 0x22: {
          const b = D[sp - 1], a = D[sp - 2];
          let r: number;
          if (op === 0x10) r = (a + b) | 0;
          else if (op === 0x11) r = (a - b) | 0;
          else if (op === 0x12) r = Math.imul(a, b);
          else if (op === 0x13) { if (b === 0) throw 4; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
          else if (op === 0x14) { if (b === 0) throw 4; r = b === -1 ? 0 : a % b; }
          else if (op === 0x15) { if (b === 0) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
          else if (op === 0x16) { if (b === 0) throw 4; r = (a >>> 0) % (b >>> 0) | 0; }
          else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
          D[sp - 2] = r; sp--;
          break;
        }
        case 0x30: case 0x31: case 0x32: {
          const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
          let take = true;
          if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
          if (take) pc = nx + rel;
          break;
        }
        case 0x33:
          if (csp === 64) throw 7;
          C[csp++] = nx;
          pc = p[nx - 2] | (p[nx - 1] << 8);
          break;
        case 0x34:
          if (csp === 0) throw 8;
          pc = C[--csp];
          break;
        case 0x40: case 0x41: {
          const a = D[sp - 1];
          if (a < 0 || a > 255) throw 6;
          if (op === 0x40) D[sp - 1] = M[a];
          else { M[a] = D[sp - 2]; sp -= 2; }
          break;
        }
        case 0x50: {
          const s = String(D[sp - 1]);
          if (olen + s.length > 65536) throw 11;
          sp--;
          for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
          break;
        }
        case 0x51:
          if (olen + 1 > 65536) throw 11;
          out[olen++] = D[--sp] & 255;
          break;
        case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
        case 0x53: return done(D[--sp] & 255);
      }
    }
  } catch (e) {
    if (typeof e === 'number') return done(e);
    throw e;
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp: Uint8Array;
  try { inp = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { inp = new Uint8Array(0); }
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
