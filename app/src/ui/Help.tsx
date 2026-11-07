// "Como jogar": a quick wizard, one idea per step, with something to look at. Skip at any time.
import { useEffect, useRef, useState, type ReactNode } from "react";
import { CardTile } from "./CardTile.tsx";

/** A small patch of felt with a few pieces, drawn for the explanations. */
function Felt({ children }: { children: ReactNode }) {
  return (
    <svg className="wizard-felt" viewBox="0 0 5 5" aria-hidden="true">
      {Array.from({ length: 6 }, (_, i) => (
        <g key={i} className="chalk-grid"><line x1={i} y1={0} x2={i} y2={5} /><line x1={0} y1={i} x2={5} y2={i} /></g>
      ))}
      {children}
    </svg>
  );
}
const Button = ({ x, y, side }: { x: number; y: number; side: 0 | 1 }) => (
  <g><circle cx={x + 0.5} cy={y + 0.5} r={0.34} fill={side ? "var(--red)" : "var(--blue)"} /><circle cx={x + 0.5} cy={y + 0.5} r={0.2} className="card-button-ring" /></g>
);
const Teacher = ({ x, y, side }: { x: number; y: number; side: 0 | 1 }) => (
  <g><rect x={x + 0.18} y={y + 0.22} width={0.64} height={0.56} rx={0.1} fill={side ? "var(--red)" : "var(--blue)"} /><rect x={x + 0.16} y={y + 0.44} width={0.68} height={0.12} fill="var(--brass)" /></g>
);
const Dot = ({ x, y, color }: { x: number; y: number; color: string }) => <circle cx={x + 0.5} cy={y + 0.5} r={0.14} fill={color} />;

const STEPS: { title: string; text: string; art: ReactNode }[] = [
  {
    title: "O objetivo",
    text: "Capture o goleiro do adversário (o bloco alto) ou leve qualquer botão seu até o gol dele, a casa onde o goleiro começou.",
    art: (
      <Felt>
        <rect x={1.9} y={0} width={1.2} height={0.18} className="wizard-goal" />
        <Teacher x={2} y={0} side={1} />
        <Button x={2} y={2} side={0} />
        <path d="M2.5 2.1 L2.5 1.15" className="wizard-arrow" />
      </Felt>
    ),
  },
  {
    title: "Escolha uma jogada",
    text: "Toque numa das suas duas cartas. Cada botão seu que pode andar ganha uma cor, com os pontos para onde ele pode ir.",
    art: (
      <Felt>
        <Button x={1} y={3} side={0} /><Button x={3} y={3} side={0} />
        <Dot x={1} y={2} color="#6fdcff" /><Dot x={0} y={3} color="#6fdcff" /><Dot x={2} y={3} color="#ff8fc8" />
        <Dot x={3} y={2} color="#ff8fc8" /><Dot x={4} y={3} color="#ff8fc8" />
      </Felt>
    ),
  },
  {
    title: "Toque no ponto",
    text: "Toque num ponto para mover aquele botão. Cair em cima de um botão adversário captura ele, e ele sai da mesa.",
    art: (
      <Felt>
        <Button x={2} y={3} side={0} /><Button x={2} y={1} side={1} />
        <circle cx={2.5} cy={1.5} r={0.46} className="wizard-capture" />
        <path d="M2.5 3.1 L2.5 2.1" className="wizard-arrow" />
      </Felt>
    ),
  },
  {
    title: "Como ler a carta",
    text: "O botão no meio é o seu e os círculos mostram para onde ele vai. Para cima é sempre a frente, na direção do adversário.",
    art: <CardTile id={3} side={0} />,
  },
  {
    title: "A troca",
    text: "Depois de jogar, a carta usada vai para a mesa e você fica com a que estava lá. Na vez dele, o adversário pega a sua.",
    art: (
      <div className="wizard-swap">
        <CardTile id={0} side={0} small />
        <svg viewBox="0 0 40 24" aria-hidden="true"><path d="M4 8 H32 M26 3 L32 8 L26 13 M36 18 H8 M14 13 L8 18 L14 23" className="wizard-arrow" /></svg>
        <CardTile id={6} side={0} small />
      </div>
    ),
  },
  {
    title: "As cartas do adversário",
    text: "Para ele, a frente é para baixo. Quando ele joga, a carta aparece virada, e dá para ver a jogada de novo.",
    art: <CardTile id={3} side={1} turned />,
  },
  {
    title: "Relógio e empate",
    text: "Cada jogada tem 30 segundos; se acabar, o relógio joga por você. Vinte rodadas seguidas sem captura dão empate.",
    art: <div className="wizard-clock">0:30</div>,
  },
];

// The home teaches the game first; once the tour is seen (or skipped) it goes straight to the modes.
const TOUR_KEY = "recreio.tour.done";
export const tourDone = () => { try { return localStorage.getItem(TOUR_KEY) === "1"; } catch { return false; } };
export const markTour = () => { try { localStorage.setItem(TOUR_KEY, "1"); } catch { /* private mode: the intro shows again next time */ } };

export function Help({ onClose }: { onClose: () => void }) {
  const [step, setStep] = useState(0);
  const next = useRef<HTMLButtonElement>(null);
  const last = step === STEPS.length - 1;
  useEffect(() => { next.current?.focus(); }, [step]);
  useEffect(() => {
    const key = (e: KeyboardEvent) => {
      if (e.key === "Escape") onClose();
      if (e.key === "ArrowRight") setStep((s) => Math.min(STEPS.length - 1, s + 1));
      if (e.key === "ArrowLeft") setStep((s) => Math.max(0, s - 1));
    };
    addEventListener("keydown", key);
    return () => removeEventListener("keydown", key);
  }, [onClose]);
  const s = STEPS[step];
  return (
    <div className="whistle" role="dialog" aria-modal="true" aria-labelledby="wizard-title">
      <section className="plaque wizard">
        <div className="wizard-top">
          <span className="wizard-count">{step + 1} de {STEPS.length}</span>
          <button type="button" className="link" onClick={onClose}>Pular</button>
        </div>
        <div className="wizard-art">{s.art}</div>
        <h1 id="wizard-title" className="title small">{s.title}</h1>
        <p className="lede">{s.text}</p>
        <div className="wizard-dots" aria-hidden="true">
          {STEPS.map((_, i) => <i key={i} className={i === step ? "on" : ""} />)}
        </div>
        <div className="wizard-nav">
          <button type="button" className="secondary" onClick={() => setStep(step - 1)} disabled={step === 0}>Voltar</button>
          <button ref={next} type="button" className="primary" onClick={() => (last ? onClose() : setStep(step + 1))}>{last ? "Entendi" : "Próximo"}</button>
        </div>
      </section>
    </div>
  );
}
