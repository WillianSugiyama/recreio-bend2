// The relay: one Durable Object per 6-digit room code. It pairs two browsers and forwards their
// messages. What it does with each event is decided by relay.bend (compiled to relay.mjs), whose
// laws are proven in relay/PROOF.bend; this file only turns WebSocket events into those calls.
import R from "./relay.mjs";

const idOf = (state, ws) => Number(state.getTags(ws)[0]);

// The room as relay.bend sees it: the ids of the browsers in it, in arrival order.
function seats(state) {
  const ids = state.getWebSockets().map((ws) => idOf(state, ws));
  return R.api_seats(ids.length, ids[0] ?? 0, ids[1] ?? 0);
}

// Sends what relay.bend decided: a forwarded message is the very text received.
function deliver(state, step, message) {
  for (let i = 0; i < R.api_note_count(step); i++) {
    const to = state.getWebSockets().find((ws) => idOf(state, ws) === R.api_note_to(step, i));
    const kind = R.api_note_kind(step, i);
    to?.send(kind === 0 ? message : JSON.stringify({ t: kind === 1 ? "peer" : "left" }));
  }
}

export class Room {
  constructor(state) {
    this.state = state;
  }

  async fetch(request) {
    if (request.headers.get("Upgrade") !== "websocket") return new Response("expected a websocket", { status: 426 });
    const id = crypto.getRandomValues(new Uint32Array(1))[0];
    const step = R.api_join(seats(this.state), id);
    if (!R.api_accepted(step)) return new Response("room is full", { status: 409 });
    const [client, server] = Object.values(new WebSocketPair());
    this.state.acceptWebSocket(server, [String(id)]);
    deliver(this.state, step);
    return new Response(null, { status: 101, webSocket: client });
  }

  webSocketMessage(ws, message) {
    if (typeof message !== "string") return;
    deliver(this.state, R.api_message(seats(this.state), idOf(this.state, ws), message.length, message), message);
  }

  webSocketClose(ws) {
    deliver(this.state, R.api_close(seats(this.state), idOf(this.state, ws)));
  }
}

export default {
  async fetch(request, env) {
    const m = new URL(request.url).pathname.match(/^\/room\/(\d{6})$/);
    if (!m) return new Response("recreio relay", { status: 200 });
    return env.ROOMS.get(env.ROOMS.idFromName(m[1])).fetch(request);
  },
};
