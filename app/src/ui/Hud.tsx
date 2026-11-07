// Everything around the table during a match: the opponent's hidden cards, the scoreboard,
// your cards and the table card, what to do next (with tips in the first match), and a hidden grid
// of squares for keyboards.
import { useEffect, useLayoutEffect, useRef, useState } from "react";
import { G, CELLS, W, cardName, cellAt, hand, type Side } from "../engine/index.ts";
import { TURN_SECONDS, clickSquare, myMoves, pauseClock, pickCard, replayLast, resign, resumeClock, setFocusSq, toMenu, useMatch, type State } from "../match.ts";
import { safeArea } from "../scene/safe.ts";
import { CardTile } from "./CardTile.tsx";
import { Help } from "./Help.tsx";


function Placar({ s }: { s: State }) {
  const o = s.odds;
  const total = o ? o.blue + o.red + o.draws || 1 : 1;
  const pct = (n: number) => (o ? `${Math.round((100 * n) / total)}` : "··");
  const cells: [string, string, number][] = [["Azul", "blue", o?.blue ?? 0], ["Empate", "draw", o?.draws ?? 0], ["Vermelho", "red", o?.red ?? 0]];
  return (
    <div className="placar" role="group" aria-label="Chance de vitória de cada lado">
      {cells.map(([label, key, n]) => (
        <div key={key} className={`placar-cell ${key}`}>
          <span className="placar-label">{label}</span>
          <span className="placar-num" aria-label={o ? `${pct(n)} por cento` : "calculando"}>{pct(n)}<small>%</small></span>
        </div>
      ))}
    </div>
  );
}

function status(s: State): string {
  if (!s.g) return "";
  if (s.over) return s.over.title;
  if (s.notice && performance.now() - s.notice.at < 4000) return s.notice.text;
  if (s.busy) return s.mode === "bot" ? "O bot está pensando…" : "Esperando a jogada do seu amigo…";
  if (G.api_turn(s.g) !== s.me) return "Vez do adversário.";
  if (s.cardPick == null) return "Sua vez: escolha uma carta.";
  if (s.sel == null) return "Cada cor é um botão: toque num ponto para mover.";
  return "Toque num ponto dourado para mover.";
}

/** What one look at the info plaque should tell: always exactly one thing, so the layout never jumps. */
function Info({ s }: { s: State }) {
  const g = s.g!;
  const them = (1 - s.me) as Side;
  const mine = G.api_turn(g) === s.me;
  const lastBy = s.last ? cellAt(g, s.last.to)?.owner : undefined;
  const who = (sq: number) => (cellAt(g, sq)?.teacher ? "o goleiro" : "um aluno");
  if (s.last && lastBy === them && mine) {
    return (
      <div className="info">
        <CardTile id={s.last.card} side={them} small turned label="Carta que o adversário jogou" />
        <p>
          {s.mode === "bot" ? "O bot" : "Seu amigo"} jogou <strong>{cardName(s.last.card)}</strong> com {who(s.last.to)}. Para ele, a frente é para baixo: a carta vale virada, assim.
        </p>
        <button type="button" className="info-action" onClick={replayLast} disabled={s.replaying}>{s.replaying ? "Olhe a mesa" : "Ver de novo"}</button>
      </div>
    );
  }
  if (s.last && lastBy === s.me && !mine) {
    return (
      <div className="info">
        <CardTile id={s.last.card} side={s.me} small label="Carta que você jogou" />
        <p>Você jogou <strong>{cardName(s.last.card)}</strong> com {who(s.last.to)}. Ela foi para a mesa, e você ficou com a que estava lá.</p>
      </div>
    );
  }
  return (
    <div className="info">
      <p>Toque numa jogada: cada botão seu que pode andar ganha uma cor, com os pontos para onde ele vai. Para cima é a frente.</p>
    </div>
  );
}

/** The turn clock, in the placar's style: seconds left for whoever is playing, red at the end. */
function Clock({ s }: { s: State }) {
  const [, tick] = useState(0);
  useEffect(() => { const t = setInterval(() => tick((n) => n + 1), 200); return () => clearInterval(t); }, []);
  if (!s.g || s.clockEndsAt == null || s.over) return null;
  const left = Math.max(0, (s.clockEndsAt - performance.now()) / 1000);
  const mine = G.api_turn(s.g) === s.me;
  const secs = Math.ceil(left);
  return (
    <div className={`clock ${mine ? "mine" : "theirs"} ${mine && secs <= 5 ? "urgent" : ""}`} role="timer"
      aria-label={mine ? `Seu tempo: ${secs} segundos` : `Tempo do adversário: ${secs} segundos`}>
      <span className="clock-num">0:{String(secs).padStart(2, "0")}</span>
      <span className="clock-bar"><i style={{ width: `${(100 * left) / TURN_SECONDS}%` }} /></span>
    </div>
  );
}

const quietText = (left: number) =>
  left <= 1 ? "Se ninguém capturar na próxima rodada, dá empate." : `Faltam ${left} rodadas sem captura para dar empate.`;

function MenuIcon() {
  return (
    <svg viewBox="0 0 24 24" width="22" height="22" aria-hidden="true">
      <path d="M4 7h16M4 12h16M4 17h16" stroke="currentColor" strokeWidth="2" strokeLinecap="round" />
    </svg>
  );
}

function KeyboardBoard({ s }: { s: State }) {
  const flip = s.me === 1;
  return (
    <div className="sr-only" role="grid" aria-label="Tabuleiro">
      {Array.from({ length: W }, (_, r) => (
        <div role="row" key={r}>
          {Array.from({ length: W }, (_, c) => {
            const sq = flip ? CELLS - 1 - (r * W + c) : r * W + c;
            const cell = s.g ? cellAt(s.g, sq) : null;
            const who = cell ? `${cell.teacher ? "goleiro" : "aluno"} ${cell.owner === 0 ? "azul" : "vermelho"}` : "vazia";
            return (
              <button key={c} role="gridcell" type="button" aria-label={`Casa ${sq + 1}: ${who}`}
                onFocus={() => setFocusSq(sq)} onBlur={() => setFocusSq(null)} onClick={() => clickSquare(sq)} />
            );
          })}
        </div>
      ))}
    </div>
  );
}

export function Hud() {
  const s = useMatch();
  const [sheet, setSheet] = useState(false);
  const [help, setHelpState] = useState(false);
  const setHelp = (open: boolean) => {
    if (open) pauseClock(); else resumeClock();
    setHelpState(open);
  };
  const placar = useRef<HTMLDivElement>(null);
  const bottom = useRef<HTMLElement>(null);

  // tell the camera which band of the screen the table may use
  useLayoutEffect(() => {
    const measure = () => {
      safeArea.top = placar.current?.getBoundingClientRect().bottom ?? 0;
      safeArea.bottom = bottom.current ? innerHeight - bottom.current.getBoundingClientRect().top : 0;
    };
    measure();
    const ro = new ResizeObserver(measure);
    if (placar.current) ro.observe(placar.current);
    if (bottom.current) ro.observe(bottom.current);
    addEventListener("resize", measure);
    return () => { ro.disconnect(); removeEventListener("resize", measure); safeArea.top = safeArea.bottom = 0; };
  }, []);

  if (!s.g) return null;
  const me = s.me, them = (1 - me) as Side;
  const mine = hand(s.g, me);
  const canPlay = myMoves(s).length > 0;

  const quiet = G.api_quiet(s.g);
  return (
    <>
      <header className="hud-top">
        <div className={`who ${them === 0 ? "blue" : "red"}`}>
          <span className="who-dot" />
          <span className="who-name">{s.opponent}</span>
        </div>
        <div className="hand them" aria-label="Cartas do adversário, viradas">
          <CardTile id={99} side={them} small />
          <CardTile id={99} side={them} small />
        </div>
        <button type="button" className="icon-button" aria-label="Opções da partida" aria-expanded={sheet} onClick={() => setSheet((v) => !v)}>
          <MenuIcon />
        </button>
        {sheet && (
          <div className="sheet" role="menu">
            <button type="button" role="menuitem" onClick={() => { setSheet(false); setHelp(true); }}>Como jogar</button>
            <button type="button" role="menuitem" onClick={() => { setSheet(false); resign(); }} disabled={!!s.over}>Desistir da partida</button>
            <button type="button" role="menuitem" onClick={() => { setSheet(false); toMenu(); }}>Voltar ao menu</button>
          </div>
        )}
      </header>
      <div className="placar-row" ref={placar}><Placar s={s} /></div>
      <footer className="hud-bottom" ref={bottom}>
        <div className="status-row">
          <div className="status-col">
            <p className="status" aria-live="polite">{status(s)}</p>
            {quiet >= 10 && !s.over && <p className="quiet">{quietText(20 - quiet)}</p>}
          </div>
          <Clock s={s} />
        </div>
        {!s.over && <Info s={s} />}
        <div className="tray">
          <div className="hand mine">
            {mine.map((id) => (
              <CardTile key={id} id={id} side={me} selected={s.cardPick === id} onPick={canPlay ? () => pickCard(id) : undefined} />
            ))}
          </div>
          <div className="table-slot">
            <CardTile id={G.api_table(s.g)} side={me} label="Carta da mesa" />
            <span className="table-label">Na mesa</span>
            <span className="table-hint">{G.api_turn(s.g) === me ? "Você pega depois de jogar" : "O adversário pega depois de jogar"}</span>
          </div>
        </div>
      </footer>
      <KeyboardBoard s={s} />
      {help && <Help onClose={() => setHelp(false)} />}
    </>
  );
}
