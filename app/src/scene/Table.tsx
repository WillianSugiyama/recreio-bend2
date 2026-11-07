// The futebol de botão table: felt, varnished frame, one warm lamp, and the buttons.
import { useEffect, useMemo, useRef } from "react";
import * as THREE from "three";
import { Canvas, useFrame, useThree } from "@react-three/fiber";
import { RoundedBox } from "@react-three/drei";
import { RoomEnvironment } from "three/examples/jsm/environments/RoomEnvironment.js";
import { W, CELLS, HOMES, type Move } from "../engine/index.ts";
import { clickSquare, myMoves, setFocusSq, useMatch, type PieceView } from "../match.ts";
import { FELT_SIZE, chalkGrainTexture, feltTexture, netTexture, scuffTexture, woodTexture } from "./textures.ts";
import { reducedMotion, safeArea } from "./safe.ts";

const COLORS = { blue: "#2453d4", red: "#d63a3a", brass: "#d6a43a", chalk: "#f1efe6" };
/** Colored chalk: when a card is chosen, each of your buttons that can move gets its own color. */
export const CHALK = ["#6fdcff", "#ff8fc8", "#b6f27a", "#c4a5ff", "#ffa36b", "#7ff5d1", "#fff3a3"];
const half = (W - 1) / 2;
const pos = (sq: number): [number, number] => [(sq % W) - half, Math.floor(sq / W) - half];
const easeOut = (t: number) => 1 - Math.pow(2, -10 * Math.min(1, Math.max(0, t)));

// ---- camera: behind the player, tilted, distance fitted so the whole table always fits the width

function Rig({ me, idle }: { me: number; idle: boolean }) {
  const { camera, size, scene } = useThree();
  useFrame(({ clock }) => {
    const cam = camera as THREE.PerspectiveCamera;
    const { width: Wpx, height: Hpx } = size;
    // the HUD covers the top and bottom; the table is fitted into the band between them
    const top = idle ? 0 : safeArea.top, bottom = idle ? 0 : safeArea.bottom;
    const band = Math.max(120, Hpx - top - bottom);
    const aspect = Wpx / band;
    // tall bands have height to spare: look from higher up so the table fills them
    const steep = THREE.MathUtils.clamp((1.1 - aspect) / 0.6, 0, 1);
    const elev = THREE.MathUtils.degToRad(THREE.MathUtils.lerp(52, 64, steep));
    const tan = Math.tan(THREE.MathUtils.degToRad(cam.fov / 2));
    const need = (FELT_SIZE + 1.1) / 2;
    const fitW = need / (tan * (Wpx / Hpx));
    const fitH = ((need * Math.sin(elev) + 0.35) / tan) * (Hpx / band);
    const d = Math.max(fitW, fitH) * (idle && Wpx / Hpx > 1.2 ? 1.18 : 1.01);
    const sway = idle && !reducedMotion ? Math.sin(clock.elapsedTime * 0.18) * 0.1 : 0;
    const side = me === 0 ? 1 : -1;
    const v = new THREE.Vector3(0, Math.sin(elev), Math.cos(elev)).applyAxisAngle(new THREE.Vector3(0, 1, 0), sway).multiplyScalar(d);
    cam.position.set(v.x * side, v.y, v.z * side);
    // on the menu, slide the table out from under the panel: up on phones, left on wide screens
    const look = idle ? (Wpx / Hpx > 1.2 ? [2.4, 0, 0.4] : [0, 0, 3.7]) : [0, 0, 0.15];
    cam.lookAt(look[0] * side, look[1], look[2] * side);
    // move the picture's center to the band's center
    cam.setViewOffset(Wpx, Hpx, 0, (bottom - top) / 2, Wpx, Hpx);
    // the room fades out behind the table, wherever the camera ends up
    if (scene.fog instanceof THREE.Fog) { scene.fog.near = d * 1.05; scene.fog.far = d * 2.1; }
  });
  return null;
}

// Gives the brass and the varnish something to reflect: a small studio room, built locally (no CDN).
function Reflections() {
  const { gl, scene } = useThree();
  useEffect(() => {
    const pm = new THREE.PMREMGenerator(gl);
    const env = pm.fromScene(new RoomEnvironment(), 0.04).texture;
    scene.environment = env;
    scene.environmentIntensity = 0.22;
    return () => { scene.environment = null; env.dispose(); pm.dispose(); };
  }, [gl, scene]);
  return null;
}

// ---- the buttons

const studentGeometry = (() => {
  // a lathe profile: slightly domed top, rounded rim, flat base
  const pts = [
    [0, 0], [0.33, 0], [0.37, 0.02], [0.385, 0.06], [0.38, 0.11], [0.355, 0.145], [0.3, 0.16], [0.16, 0.168], [0, 0.17],
  ].map(([x, y]) => new THREE.Vector2(x, y));
  return new THREE.LatheGeometry(pts, 48);
})();

function Piece({ p, selected, hint }: { p: PieceView; selected: boolean; hint: string | null }) {
  const ref = useRef<THREE.Group>(null);
  const anim = useRef<{ from: THREE.Vector3; to: THREE.Vector3; t0: number; dur: number; spin: number } | null>(null);
  const [x, z] = pos(p.sq);
  useEffect(() => {
    const g = ref.current;
    if (!g) return;
    const to = new THREE.Vector3(x, 0, z);
    if (g.position.lengthSq() === 0 && !anim.current) { g.position.copy(to); return; }
    const dist = g.position.distanceTo(to);
    if (dist < 0.01) return;
    anim.current = { from: g.position.clone(), to, t0: performance.now(), dur: reducedMotion ? 120 : 380 + dist * 110, spin: (Math.random() < 0.5 ? -1 : 1) * (1.6 + dist * 0.5) };
  }, [x, z]);
  useFrame(() => {
    const g = ref.current;
    if (!g) return;
    const now = performance.now();
    if (p.knock) {
      // struck off the table: slides away fast, leaves the felt, tumbles and falls out of view
      const t = (now - p.knock.at) / 1000;
      const [kx, kz] = pos(p.sq);
      g.position.set(kx + p.knock.dx * t * 7, Math.max(-6, 0.25 * Math.sin(Math.min(t, 0.25) * 12) - (t > 0.3 ? (t - 0.3) ** 2 * 12 : 0)), kz + p.knock.dz * t * 7);
      g.rotation.set(t * 9 * p.knock.dz, t * 4, -t * 9 * p.knock.dx);
      g.visible = t < 1.6;
      return;
    }
    // a button on the board is always shown upright: nothing carries over from a knock-off
    g.visible = true;
    g.rotation.x = 0;
    g.rotation.z = 0;
    const a = anim.current;
    if (a) {
      const k = (now - a.t0) / a.dur, e = easeOut(k);
      g.position.lerpVectors(a.from, a.to, e);
      g.rotation.y += a.spin * (1 - e) * 0.016;
      if (k >= 1) anim.current = null;
    }
    const lift = selected ? 0.07 : 0;
    g.position.y += (lift - g.position.y) * 0.25;
  });
  const color = p.owner === 0 ? COLORS.blue : COLORS.red;
  return (
    <group ref={ref} userData={{ piece: true, owner: p.owner, teacher: p.teacher, knocked: !!p.knock }}>
      {p.teacher ? (
        <group>
          <RoundedBox args={[0.6, 0.58, 0.44]} radius={0.08} smoothness={4} position={[0, 0.29, 0]} castShadow>
            <meshPhysicalMaterial color={color} roughness={0.3} clearcoat={1} clearcoatRoughness={0.12} />
          </RoundedBox>
          <mesh position={[0, 0.29, 0]} castShadow>
            <boxGeometry args={[0.625, 0.1, 0.465]} />
            <meshStandardMaterial color="#e8bb52" metalness={0.85} roughness={0.28} envMapIntensity={3.2} />
          </mesh>
          <mesh position={[0, 0.582, 0]} rotation={[-Math.PI / 2, 0, 0]}>
            <ringGeometry args={[0.12, 0.155, 40]} />
            <meshStandardMaterial color={COLORS.chalk} roughness={0.5} />
          </mesh>
        </group>
      ) : (
        <group>
          <mesh geometry={studentGeometry} castShadow>
            <meshPhysicalMaterial color={color} roughness={0.28} clearcoat={1} clearcoatRoughness={0.1} />
          </mesh>
          <mesh position={[0, 0.172, 0]} rotation={[-Math.PI / 2, 0, 0]}>
            <ringGeometry args={[0.2, 0.235, 40]} />
            <meshStandardMaterial color={COLORS.chalk} roughness={0.5} />
          </mesh>
        </group>
      )}
      {(selected || hint) && (
        <mesh position={[0, 0.006, 0]} rotation={[-Math.PI / 2, 0, 0]}>
          <ringGeometry args={[p.teacher ? 0.5 : 0.43, p.teacher ? 0.56 : 0.49, 48]} />
          <meshBasicMaterial color={selected ? COLORS.brass : (hint ?? COLORS.brass)} transparent opacity={1} toneMapped={false} />
        </mesh>
      )}
    </group>
  );
}

// ---- targets, the last move's chalk scuff, and the squares you can tap

function Target({ sq, capture, colors = [COLORS.brass] }: { sq: number; capture: boolean; colors?: string[] }) {
  const group = useRef<THREE.Group>(null);
  const [x, z] = pos(sq);
  // a target settles into view once and then stays still
  const born = useMemo(() => performance.now(), []);
  useFrame(() => { if (group.current) group.current.scale.setScalar(reducedMotion ? 1 : 0.6 + 0.4 * easeOut((performance.now() - born) / 260)); });
  const n = colors.length, slice = (Math.PI * 2) / n;
  return (
    <group ref={group} position={[x, 0.009, z]} rotation={[-Math.PI / 2, 0, 0]}>
      {colors.map((c, i) => (
        <mesh key={i}>
          {capture
            ? <ringGeometry args={[0.42, 0.52, 48, 1, Math.PI / 2 + i * slice, slice]} />
            : <circleGeometry args={[n > 1 ? 0.21 : 0.17, 40, Math.PI / 2 + i * slice, slice]} />}
          <meshBasicMaterial color={c} toneMapped={false} />
        </mesh>
      ))}
      {!capture && n === 1 && <mesh><ringGeometry args={[0.3, 0.34, 48]} /><meshBasicMaterial color={colors[0]} transparent opacity={0.55} toneMapped={false} /></mesh>}
      {!capture && n > 1 && <mesh><ringGeometry args={[0.21, 0.24, 48]} /><meshBasicMaterial color={COLORS.chalk} toneMapped={false} /></mesh>}
    </group>
  );
}

// ---- chalk arrows: a slightly bent, tapering stroke with a head, drawn from a button to a destination

const grain = chalkGrainTexture();

function arrowGeometry(x0: number, z0: number, x1: number, z1: number, bend: number) {
  const dx = x1 - x0, dz = z1 - z0, len = Math.hypot(dx, dz) || 1;
  const ux = dx / len, uz = dz / len, nx = -uz, nz = ux;
  // leave the button and stop short of the dot
  const sx = x0 + ux * 0.4, sz = z0 + uz * 0.4, ex = x1 - ux * 0.3, ez = z1 - uz * 0.3;
  const cx = (sx + ex) / 2 + nx * bend * len, cz = (sz + ez) / 2 + nz * bend * len;
  const at = (t: number) => {
    const a = (1 - t) * (1 - t), b = 2 * (1 - t) * t, c = t * t;
    return [a * sx + b * cx + c * ex, a * sz + b * cz + c * ez];
  };
  const pos: number[] = [], uv: number[] = [], idx: number[] = [];
  const N = 18, headLen = 0.2;
  const shaftEnd = Math.max(0.2, 1 - headLen / Math.max(0.4, len));
  for (let i = 0; i <= N; i++) {
    const t = (i / N) * shaftEnd, [px, pz] = at(t), [qx, qz] = at(Math.min(1, t + 0.01));
    const tl = Math.hypot(qx - px, qz - pz) || 1, tnx = -(qz - pz) / tl, tnz = (qx - px) / tl;
    const half = 0.045 * (1 - 0.35 * (i / N));            // tapers toward the head
    pos.push(px + tnx * half, 0, pz + tnz * half, px - tnx * half, 0, pz - tnz * half);
    uv.push(t * len * 2.2, 1, t * len * 2.2, 0);
    if (i < N) { const k = i * 2; idx.push(k, k + 1, k + 2, k + 1, k + 3, k + 2); }
  }
  // the head: a triangle along the curve's last direction
  const [hx, hz] = at(shaftEnd), [tx, tz] = at(1);
  const hl = Math.hypot(tx - hx, tz - hz) || 1, hnx = -(tz - hz) / hl, hnz = (tx - hx) / hl;
  const base = pos.length / 3;
  pos.push(hx + hnx * 0.12, 0, hz + hnz * 0.12, hx - hnx * 0.12, 0, hz - hnz * 0.12, tx, 0, tz);
  uv.push(0.2, 1, 0.2, 0, 0.6, 0.5);
  idx.push(base, base + 1, base + 2);
  const g = new THREE.BufferGeometry();
  g.setAttribute("position", new THREE.Float32BufferAttribute(pos, 3));
  g.setAttribute("uv", new THREE.Float32BufferAttribute(uv, 2));
  g.setIndex(idx);
  return g;
}

function Arrow({ from, to, color, bend }: { from: number; to: number; color: string; bend: number }) {
  const [x0, z0] = pos(from), [x1, z1] = pos(to);
  const geo = useMemo(() => arrowGeometry(x0, z0, x1, z1, bend), [x0, z0, x1, z1, bend]);
  useEffect(() => () => geo.dispose(), [geo]);
  return (
    <mesh geometry={geo} position={[0, 0.012, 0]}>
      <meshBasicMaterial color={color} alphaMap={grain} transparent opacity={0.92} depthWrite={false} toneMapped={false} side={THREE.DoubleSide} />
    </mesh>
  );
}

const scuffMap = scuffTexture();

function Scuff({ last, persist }: { last: Move & { at: number }; persist: boolean }) {
  const ref = useRef<THREE.MeshBasicMaterial>(null);
  const [x0, z0] = pos(last.from), [x1, z1] = pos(last.to);
  const len = Math.hypot(x1 - x0, z1 - z0);
  // the opponent's last move stays readable until you answer it; your own fades away
  useFrame(() => { if (ref.current) ref.current.opacity = persist ? 0.7 : Math.max(0, 0.75 * (1 - (performance.now() - last.at) / 4000)); });
  return (
    <mesh position={[(x0 + x1) / 2, 0.004, (z0 + z1) / 2]} rotation={[-Math.PI / 2, 0, -Math.atan2(z1 - z0, x1 - x0)]}>
      <planeGeometry args={[len + 0.3, 0.2]} />
      <meshBasicMaterial ref={ref} map={scuffMap} color={COLORS.chalk} transparent depthWrite={false} />
    </mesh>
  );
}

function Squares({ active }: { active: Set<number> }) {
  const plane = useMemo(() => new THREE.PlaneGeometry(0.98, 0.98), []);
  return (
    <group>
      {Array.from({ length: CELLS }, (_, sq) => {
        const [x, z] = pos(sq);
        return (
          <mesh key={sq} geometry={plane} position={[x, 0.01, z]} rotation={[-Math.PI / 2, 0, 0]}
            onClick={(e) => { e.stopPropagation(); clickSquare(sq); }}
            onPointerOver={() => { if (active.has(sq)) document.body.style.cursor = "pointer"; }}
            onPointerOut={() => { document.body.style.cursor = ""; }}>
            <meshBasicMaterial visible={false} />
          </mesh>
        );
      })}
    </group>
  );
}

// ---- the goals: a futsal goal standing on each goalkeeper's home square, the goalkeeper inside it

const POST = 0.05;

function netMaterial(repeat: number) {
  const map = netTexture();
  map.repeat.set(repeat, repeat);
  return new THREE.MeshStandardMaterial({ map, transparent: true, side: THREE.DoubleSide, depthWrite: false, roughness: 0.9, color: "#e9e6dc" });
}

function Goal({ sq }: { sq: number }) {
  const [x, z] = pos(sq);
  const out = z < 0 ? -1 : 1;                  // which board edge this goal backs onto
  // a futsal goal on the goalkeeper's own square: posts and crossbar at the mouth (facing the pitch),
  // the net falling from the crossbar to the ground at the board's edge, triangles of net at the sides
  const w = 0.96, h = 0.66, d = 0.9;
  const line = z - out * (d / 2), back = z + out * (d / 2);
  const slope = Math.hypot(d, h);
  const backNet = useMemo(() => { const m = netMaterial(1); m.map!.repeat.set(w * 9, slope * 9); return m; }, [slope]);
  const sideNet = useMemo(() => netMaterial(9), []);
  const side = useMemo(() => {
    const sh = new THREE.Shape();
    sh.moveTo(line, 0); sh.lineTo(line, h); sh.lineTo(back, 0); sh.closePath();
    return new THREE.ShapeGeometry(sh);
  }, [line, back]);
  const white = <meshStandardMaterial color="#f6f4ee" roughness={0.3} metalness={0.15} />;
  return (
    <group>
      {[-1, 1].map((sx) => (
        <mesh key={sx} position={[x + (sx * w) / 2, h / 2, line]} castShadow>
          <cylinderGeometry args={[POST, POST, h, 14]} />{white}
        </mesh>
      ))}
      <mesh position={[x, h, line]} rotation={[0, 0, Math.PI / 2]} castShadow>
        <cylinderGeometry args={[POST, POST, w + POST * 2, 14]} />{white}
      </mesh>
      <mesh position={[x, 0.025, back]} rotation={[0, 0, Math.PI / 2]}>
        <cylinderGeometry args={[POST * 0.6, POST * 0.6, w, 10]} />{white}
      </mesh>
      <mesh position={[x, h / 2, (line + back) / 2]} rotation={[Math.atan2(-out * d, h), 0, 0]} material={backNet}>
        <planeGeometry args={[w, slope]} />
      </mesh>
      {[-1, 1].map((sx) => (
        <mesh key={`s${sx}`} geometry={side} position={[x + (sx * w) / 2, 0, 0]} rotation={[0, -Math.PI / 2, 0]} material={sideNet} />
      ))}
    </group>
  );
}

// where the opponent's button left from: a chalk ring on the felt
function FromMark({ sq }: { sq: number }) {
  const [x, z] = pos(sq);
  return (
    <mesh position={[x, 0.006, z]} rotation={[-Math.PI / 2, 0, 0]}>
      <ringGeometry args={[0.3, 0.36, 40]} />
      <meshBasicMaterial color={COLORS.chalk} transparent opacity={0.7} toneMapped={false} />
    </mesh>
  );
}

function FocusMark({ sq }: { sq: number }) {
  const [x, z] = pos(sq);
  return (
    <mesh position={[x, 0.007, z]} rotation={[-Math.PI / 2, 0, 0]}>
      <ringGeometry args={[0.46, 0.5, 4, 1, Math.PI / 4]} />
      <meshBasicMaterial color={COLORS.chalk} toneMapped={false} />
    </mesh>
  );
}

// ---- the table itself

function Board() {
  const felt = useMemo(() => feltTexture(), []);
  const wood = useMemo(() => woodTexture(), []);
  const rail = 0.5, h = 0.32, out = FELT_SIZE / 2 + rail / 2;
  const rails: [number, number, number, number][] = [
    [0, -out, FELT_SIZE + rail * 2, rail], [0, out, FELT_SIZE + rail * 2, rail],
    [-out, 0, rail, FELT_SIZE], [out, 0, rail, FELT_SIZE],
  ];
  return (
    <group>
      <mesh rotation={[-Math.PI / 2, 0, 0]} receiveShadow>
        <planeGeometry args={[FELT_SIZE, FELT_SIZE]} />
        <meshStandardMaterial map={felt} roughness={0.95} />
      </mesh>
      {rails.map(([x, z, w, d], i) => (
        <mesh key={i} position={[x, h / 2 - 0.06, z]} castShadow receiveShadow>
          <boxGeometry args={[w, h, d]} />
          <meshPhysicalMaterial map={wood} roughness={0.38} clearcoat={0.9} clearcoatRoughness={0.2} />
        </mesh>
      ))}
      {[[-1, -1], [1, -1], [-1, 1], [1, 1]].map(([sx, sz], i) => (
        <mesh key={i} position={[sx * out, h - 0.055, sz * out]}>
          <cylinderGeometry args={[0.07, 0.07, 0.03, 20]} />
          <meshStandardMaterial color={COLORS.brass} metalness={1} roughness={0.3} />
        </mesh>
      ))}
      <mesh position={[0, -0.075, 0]} rotation={[-Math.PI / 2, 0, 0]} receiveShadow>
        <planeGeometry args={[80, 80]} />
        <meshStandardMaterial color="#3a2414" roughness={0.92} />
      </mesh>
    </group>
  );
}

function World() {
  const s = useMatch();
  const moves = myMoves(s);
  const withCard = moves.filter((m) => m.card === s.cardPick);
  const targets = withCard.filter((m) => m.from === s.sel);
  // with a card chosen and no button yet, every movable button shows all its paths in its own color
  const preview = s.sel == null ? withCard : [];
  const mineById = s.pieces.filter((p) => p.alive && p.owner === s.me).sort((a, b) => a.id - b.id);
  const colorOf = new Map(mineById.map((p, i) => [p.sq, CHALK[i % CHALK.length]]));
  const movable = new Set(preview.map((m) => m.from));
  const sharers = new Map<number, number[]>();
  for (const m of preview) sharers.set(m.to, [...(sharers.get(m.to) ?? []), m.from]);
  const active = new Set<number>([...targets.map((m) => m.to), ...preview.map((m) => m.to), ...s.pieces.filter((p) => p.alive && p.owner === s.me).map((p) => p.sq)]);
  const occupied = new Set(s.pieces.filter((p) => p.alive).map((p) => p.sq));
  const lastTheirs = !!s.last && s.pieces.some((p) => p.alive && p.sq === s.last!.to && p.owner !== s.me);
  return (
    <>
      <Rig me={s.me} idle={s.screen !== "game"} />
      <color attach="background" args={["#0f0b08"]} />
      <fog attach="fog" args={["#0f0b08", 16, 34]} />
      <Reflections />
      <ambientLight intensity={0.07} color="#ffe2c2" />
      <hemisphereLight args={["#ffdcb0", "#120a05", 0.08]} />
      <spotLight position={[0.3, 10, 1.2]} angle={0.52} penumbra={0.55} intensity={560} decay={2} color="#ffd6a0" castShadow
        shadow-mapSize={[2048, 2048]} shadow-bias={-0.0004} shadow-radius={5} />
      <Board />
      <DevProbe />
      {HOMES.map((sq) => <Goal key={sq} sq={sq} />)}
      {s.screen === "game" && <Squares active={active} />}
      {s.last && s.screen === "game" && <Scuff key={s.last.at} last={s.last} persist={lastTheirs} />}
      {s.last && s.screen === "game" && lastTheirs && <FromMark sq={s.last.from} />}
      {targets.map((m) => <Arrow key={`a${m.to}`} from={m.from} to={m.to} color={COLORS.brass} bend={0.12} />)}
      {targets.map((m) => <Target key={m.to} sq={m.to} capture={occupied.has(m.to)} />)}
      {preview.map((m) => {
        // arrows into a shared square bend to alternate sides, so they do not lie on top of each other
        const all = sharers.get(m.to) ?? [m.from], k = all.indexOf(m.from);
        const bend = all.length > 1 ? (k % 2 ? -1 : 1) * (0.1 + 0.06 * Math.floor(k / 2)) : 0.1;
        return <Arrow key={`p${m.from}-${m.to}`} from={m.from} to={m.to} color={colorOf.get(m.from) ?? COLORS.chalk} bend={bend} />;
      })}
      {[...sharers].map(([to, froms]) => (
        <Target key={to} sq={to} capture={occupied.has(to)} colors={froms.map((f) => colorOf.get(f) ?? COLORS.chalk)} />
      ))}
      {s.focusSq != null && <FocusMark sq={s.focusSq} />}
      {s.pieces.map((p) => <Piece key={p.id} p={p} selected={p.alive && p.sq === s.sel} hint={p.alive && movable.has(p.sq) ? (colorOf.get(p.sq) ?? null) : null} />)}
    </>
  );
}

// dev only: what is actually drawn (visible buttons and the square under each), for the browser test
function DevProbe() {
  const scene = useThree((s) => s.scene);
  useEffect(() => {
    if (!import.meta.env.DEV) return;
    Object.assign(window, {
      __drawn: () => {
        const out: { sq: number; owner: number; teacher: boolean }[] = [];
        scene.traverse((o) => {
          if (o.userData.piece && o.visible) out.push({ sq: Math.round(o.position.z + half) * W + Math.round(o.position.x + half), owner: o.userData.owner, teacher: o.userData.teacher });
        });
        return out;
      },
    });
  }, [scene]);
  return null;
}

export function Table() {
  useEffect(() => () => setFocusSq(null), []);
  return (
    <Canvas className="table-canvas" shadows={{ type: THREE.PCFSoftShadowMap }} dpr={[1, 2]} camera={{ fov: 34, near: 0.5, far: 120 }}
      gl={{ antialias: true }} onPointerMissed={() => undefined}>
      <World />
    </Canvas>
  );
}
