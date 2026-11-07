// A move card: a thick printed tile whose face is a patch of the table's felt with the move in chalk.
import { cardName, cardSteps, UNKNOWN, type Side } from "../engine/index.ts";

const TEAM = ["var(--blue)", "var(--red)"];

function Face({ id, side }: { id: number; side: Side }) {
  const steps = cardSteps(id);
  return (
    <svg className="card-felt" viewBox="0 0 7 7" aria-hidden="true">
      {Array.from({ length: 8 }, (_, i) => (
        <g key={i} className="chalk-grid">
          <line x1={i} y1={0} x2={i} y2={7} />
          <line x1={0} y1={i} x2={7} y2={i} />
        </g>
      ))}
      {steps.map(([dx, dy]) => (
        <circle key={`${dx},${dy}`} className="chalk-target" cx={3.5 + dx} cy={3.5 - dy} r={0.3} />
      ))}
      <circle cx={3.5} cy={3.5} r={0.36} fill={TEAM[side]} className="card-button" />
      <circle cx={3.5} cy={3.5} r={0.2} className="card-button-ring" />
    </svg>
  );
}

/** `turned`: the face drawn upside down, as the opponent plays it (their forward is your down). */
export function CardTile({ id, side, selected, onPick, small, label, turned }: { id: number; side: Side; selected?: boolean; onPick?: () => void; small?: boolean; label?: string; turned?: boolean }) {
  if (id === UNKNOWN) {
    return (
      <span className={`card back ${small ? "small" : ""}`} data-side={side} aria-label="Carta escondida do adversário">
        <svg viewBox="0 0 40 56" aria-hidden="true">
          <rect x="3" y="3" width="34" height="50" rx="3" className="back-frame" />
          <circle cx="20" cy="28" r="9" className="back-button" />
          <circle cx="20" cy="28" r="5" className="back-button-ring" />
        </svg>
      </span>
    );
  }
  const name = cardName(id);
  const body = (
    <>
      <Face id={id} side={side} />
      <span className="card-band"><span className={`card-name ${name.length >= 13 ? "longer" : name.length >= 10 ? "long" : ""}`}>{name}</span></span>
    </>
  );
  if (!onPick) return <span className={`card ${small ? "small" : ""} ${turned ? "turned" : ""}`} aria-label={`${label ?? "Carta"}: ${name}`}>{body}</span>;
  return (
    <button type="button" className={`card ${small ? "small" : ""}`} aria-pressed={!!selected} aria-label={`Carta ${name}`} onClick={onPick}>
      {body}
    </button>
  );
}
