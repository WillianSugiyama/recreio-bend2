import { StrictMode, useEffect } from "react";
import { createRoot } from "react-dom/client";
import "@fontsource/big-shoulders-display/800";
import "@fontsource/big-shoulders-display/900";
import "@fontsource/barlow/400.css";
import "@fontsource/barlow/500.css";
import "@fontsource/barlow/600.css";
import "@fontsource/barlow/700.css";
import "./styles.css";
import { Table } from "./scene/Table.tsx";
import { G } from "./engine/index.ts";
import { Hud } from "./ui/Hud.tsx";
import { GameOver, Menu } from "./ui/Screens.tsx";
import * as match from "./match.ts";
import { useMatch } from "./match.ts";

// dev only: lets the screenshot scripts drive a match without hunting pixels on the canvas
if (import.meta.env.DEV) Object.assign(window, { __match: match, __G: G });

function App() {
  const s = useMatch();
  useEffect(() => { document.body.dataset.screen = s.screen; }, [s.screen]);
  return (
    <div className={`app screen-${s.screen}`}>
      <div className="room-light" aria-hidden="true" />
      <div className="stage"><Table /></div>
      {s.screen === "menu" && <div className="overlay"><Menu /></div>}
      {s.screen === "game" && <Hud />}
      <GameOver />
    </div>
  );
}

createRoot(document.getElementById("root")!).render(<StrictMode><App /></StrictMode>);
