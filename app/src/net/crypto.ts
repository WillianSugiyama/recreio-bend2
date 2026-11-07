// Math for the card draw without a dealer ("mental poker", SRA with one key per card).
// Locking a card is x^k mod P; locks commute, so two players can lock and unlock in any order.
// P is the RFC 3526 2048-bit safe prime; cards live in its subgroup of squares, of prime order Q.

export const P = BigInt("0xffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca18217c32905e462e36ce3be39e772c180e86039b2783a2ec07a28fb5c55df06f4c52c9de2bcbf6955817183995497cea956ae515d2261898fa051015728e5a8aacaa68ffffffffffffffff");
export const Q = (P - 1n) / 2n;

export function modPow(b: bigint, e: bigint, m: bigint = P): bigint {
  let r = 1n;
  b %= m;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1n;
  }
  return r;
}

export function inv(a: bigint, m: bigint = Q): bigint {
  let [r0, r1, s0, s1] = [a % m, m, 1n, 0n];
  while (r1) { const q = r0 / r1; [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; }
  if (r0 !== 1n) throw new Error("no inverse");
  return ((s0 % m) + m) % m;
}

const hex = (bytes: Uint8Array): string => [...bytes].map((b) => b.toString(16).padStart(2, "0")).join("");
export const randomHex = (n: number): string => hex(crypto.getRandomValues(new Uint8Array(n)));

// A secret lock key: uniform enough in [2, Q-1] (Q is prime, so every such key can be undone).
export function randKey(): bigint {
  return (BigInt("0x" + randomHex(272)) % (Q - 2n)) + 2n;
}

function randBelow(n: number): number {
  const lim = Math.floor(0x100000000 / n) * n;
  for (;;) { const x = crypto.getRandomValues(new Uint32Array(1))[0]; if (x < lim) return x % n; }
}

export function shuffle<T>(xs: T[]): T[] {
  const a = [...xs];
  for (let i = a.length - 1; i > 0; i--) { const j = randBelow(i + 1); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}

export async function sha256(text: string): Promise<string> {
  return hex(new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(text))));
}

// The 18 cards as group elements: (i + 2)^2 mod P is a square, so it lies in the order-Q subgroup.
export const CARD_VALUES = Array.from({ length: 18 }, (_, i) => (BigInt(i + 2) ** 2n) % P);
