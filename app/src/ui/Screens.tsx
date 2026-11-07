// The screens before and after a match: menu, odd-or-even, and the final whistle.
import { useState } from "react";
import { Help, markTour, tourDone } from "./Help.tsx";
import { again, createRoom, joinRoom, playBot, setLevel, toMenu, useMatch } from "../match.ts";

const LEVELS = ["Fácil", "Médio", "Difícil"];

export function Menu() {
  const s = useMatch();
  const [code, setCode] = useState("");
  const [help, setHelp] = useState(false);
  const [intro, setIntro] = useState(() => !tourDone());
  const learned = () => { markTour(); setHelp(false); setIntro(false); };
  if (intro) return (
    <section className="plaque menu" aria-labelledby="title">
      <h1 id="title" className="title">Recreio</h1>
      <p className="lede">Um xadrez de futsal: futebol de botão em que cada jogada sai de uma carta.</p>
      <ol className="how">
        <li><b>O time.</b> Seis alunos e um goleiro de cada lado, num campo de 7 por 7.</li>
        <li><b>As cartas.</b> Você tem duas; cada uma mostra para onde um botão pode ir. Depois de jogar, ela vai para a mesa e você fica com a que estava lá.</li>
        <li><b>O gol.</b> Ganha quem capturar o goleiro adversário ou levar qualquer botão até o gol dele.</li>
      </ol>
      <button type="button" className="primary" onClick={() => setHelp(true)} autoFocus>Aprender a jogar · 1 min</button>
      <button type="button" className="link" onClick={learned}>Já sei jogar</button>
      {help && <Help onClose={learned} />}
    </section>
  );
  return (
    <section className="plaque menu" aria-labelledby="title">
      <h1 id="title" className="title">Recreio</h1>
      <p className="lede">Um xadrez de futsal: capture o goleiro ou chegue no gol dele.</p>
      <button type="button" className="link start" onClick={() => setHelp(true)}>Como jogar</button>
      {help && <Help onClose={() => setHelp(false)} />}
      <div className="group">
        <h2>Contra o bot</h2>
        <div className="segmented" role="radiogroup" aria-label="Nível do bot">
          {LEVELS.map((l, i) => (
            <button key={l} type="button" role="radio" aria-checked={s.level === i} onClick={() => setLevel(i)}>{l}</button>
          ))}
        </div>
        <button type="button" className="primary" onClick={playBot}>Jogar contra o bot</button>
      </div>
      <div className="group">
        <h2>Com um amigo</h2>
        <button type="button" className="secondary" onClick={createRoom}>Criar sala</button>
        <form className="join" onSubmit={(e) => { e.preventDefault(); if (/^\d{6}$/.test(code)) joinRoom(code); }}>
          <input inputMode="numeric" pattern="[0-9]{6}" maxLength={6} placeholder="Código da sala" aria-label="Código da sala, 6 dígitos"
            value={code} onChange={(e) => setCode(e.target.value.replace(/\D/g, ""))} />
          <button type="submit" className="secondary" disabled={code.length !== 6}>Entrar</button>
        </form>
        {s.room && (
          <p className={`room ${s.room.error ? "error" : ""}`} role="status">
            {s.room.host && !s.room.error && <span className="room-code">{s.room.code}</span>}
            {s.room.status}
          </p>
        )}
      </div>
    </section>
  );
}

export function GameOver() {
  const s = useMatch();
  if (!s.over) return null;
  return (
    <div className="whistle" role="dialog" aria-modal="true" aria-labelledby="over-title">
      <section className={`plaque over ${s.over.won === true ? "won" : s.over.won === false ? "lost" : "draw"}`}>
        <h1 id="over-title" className="title small">{s.over.title}</h1>
        <p className="lede">{s.over.reason}</p>
        {s.mode === "bot" && <button type="button" className="primary" onClick={again} autoFocus>Jogar de novo</button>}
        <button type="button" className="secondary" onClick={toMenu}>Voltar ao menu</button>
      </section>
    </div>
  );
}
