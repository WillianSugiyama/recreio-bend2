function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT" : a === b ? "EQ" : "GT"};
}

function tup_new(a, b) {
  return {$: "Tuple", fst: a, snd: b};
}

function nat_divmod(a, b) {
  return tup_new(b && Math.trunc(a / b), b ? a % b : a);
}

function nat_chk(n) {
  if (n > 281474976710655) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function nat_in(n) {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {
    throw "bend: expected a Nat host number: an integer from 0 to 2^53";
  }
  return n;
}

function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && f32_round(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace("Infinity", "inf");
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^[\t\n\v\f\r ]*[+-]?((\d+(?:\.\d*)?|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  return re.test(s) ? {$: "Some", value: f32_round(
    s.replace(/inf\w*/i, "Infinity"))} : {$: "None"};
}

const f32_round = function f32_round(s) {
  const d = Number(s);
  const a = Math.abs(d);
  const f = Math.fround(a);
  const g = 2 * a - Math.min(f, 2 ** 128);
  if (g === f || Math.fround(g) !== g || g === Infinity) {
    return Math.sign(d) * f;
  }
  let k = 0;
  while (a * 2 ** k % 1 !== 0) {
    k += 1;
  }
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s);
  const n = Number(e ?? 0) - r.length;
  const x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0));
  const y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
  return Math.sign(d) * (x === y || x > y !== g > f ? f : g);
};

const char_new = function char_new(c) {
  return c < 55296 || c >= 57344 && c <= 1114111 ? String.fromCodePoint(c) : String.fromCharCode(56320, c >>> 22, c >>> 11 & 2047, c & 2047);
};

function char_len(s, at = 0) {
  return s[at] === "\uDC00" ? 4 : s.codePointAt(at) > 0xFFFF ? 2 : 1;
}

function char_code(s) {
  return s.length < 4 ? s.codePointAt(0)
    : (s.charCodeAt(1) << 22 | s.charCodeAt(2) << 11 | s.charCodeAt(3)) >>> 0;
}

function string_contains(s, p) {
  // A match starts at a Char, not inside a packed U32 code.
  for (let at = 0; at <= s.length; at += char_len(s, at)) {
    if (s.startsWith(p, at)) {
      return true;
    }
  }
  return false;
}

function str_out(s) {
  return s.replace(/\uDC00[^]{3}/gu, "\uFFFD");
}

function str_in(s) {
  return s.replace(/\p{Cs}/gu, "\uFFFD");
}

// Array
// =====

function array_new(d, v, lgs) {
  if (d > 31 - lgs) {
    throw "bend: an array past the deepest block class 31 (depth + log2 words per cell)";
  }
  return Array(2 ** d).fill(v);
}

function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_rmw(a, i, f) {
  const old = a[i %= a.length];
  a[i] = f(old);
  return tup_new(a, old);
}

// Run
// ===

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}

// Effect
// ======

const $0eff = Object.create(null);
const io_file_append = new Set();

function io_eff(k, run) {
  if (arguments.length > 2) {
    throw new Error("bend: " + k + " takes no need: an effect that waits parks itself");
  }
  if (k in $0eff) {
    throw new Error("bend: two effects register " + k);
  }
  $0eff[k] = run;
}
// Program
// =======

function $MAX() {
  return 65536;
}

function $room_join_one(_same_0, _a_0, _id_0) {
  if (_same_0) {
    return {$: "RStep", "seats": {$: "One", "a": _a_0}, "accepted": false, "out": {$: "Nil"}};
  } else {
    return {$: "RStep", "seats": {$: "Two", "a": _a_0, "b": _id_0}, "accepted": true, "out": {$: "Con", "head": {$: "Joined", "to": _a_0}, "tail": {$: "Con", "head": {$: "Joined", "to": _id_0}, "tail": {$: "Nil"}}}};
  }
}

function $room_join(_s_0, _id_0) {
  if (_s_0.$ === "Empty") {
    return {$: "RStep", "seats": {$: "One", "a": _id_0}, "accepted": true, "out": {$: "Nil"}};
  } else if (_s_0.$ === "One") {
    const _a_0 = _s_0["a"];
    return $room_join_one((_a_0 === _id_0), _a_0, _id_0);
  } else {
    const _a_1 = _s_0["a"];
    const _b_0 = _s_0["b"];
    return {$: "RStep", "seats": {$: "Two", "a": _a_1, "b": _b_0}, "accepted": false, "out": {$: "Nil"}};
  }
}

function $room_forward_two(_from_a_0, _from_b_0, _a_0, _b_0, _text_0) {
  if (_from_a_0) {
    return {$: "Con", "head": {$: "Forward", "to": _b_0, "text": _text_0}, "tail": {$: "Nil"}};
  } else {
    if (_from_b_0) {
      return {$: "Con", "head": {$: "Forward", "to": _a_0, "text": _text_0}, "tail": {$: "Nil"}};
    } else {
      return {$: "Nil"};
    }
  }
}

function $room_forward(_s_0, _from_0, _text_0) {
  if (_s_0.$ === "Two") {
    const _a_0 = _s_0["a"];
    const _b_0 = _s_0["b"];
    return $room_forward_two((_from_0 === _a_0), (_from_0 === _b_0), _a_0, _b_0, _text_0);
  } else {
    return {$: "Nil"};
  }
}

function $room_say(_fits_0, _s_0, _from_0, _text_0) {
  if (_fits_0) {
    return {$: "RStep", "seats": _s_0, "accepted": true, "out": $$room_forward(_s_0, _from_0, _text_0)};
  } else {
    return {$: "RStep", "seats": _s_0, "accepted": true, "out": {$: "Nil"}};
  }
}

function $room_leave_two(_is_a_0, _is_b_0, _a_0, _b_0) {
  if (_is_a_0) {
    return {$: "RStep", "seats": {$: "One", "a": _b_0}, "accepted": true, "out": {$: "Con", "head": {$: "Gone", "to": _b_0}, "tail": {$: "Nil"}}};
  } else {
    if (_is_b_0) {
      return {$: "RStep", "seats": {$: "One", "a": _a_0}, "accepted": true, "out": {$: "Con", "head": {$: "Gone", "to": _a_0}, "tail": {$: "Nil"}}};
    } else {
      return {$: "RStep", "seats": {$: "Two", "a": _a_0, "b": _b_0}, "accepted": true, "out": {$: "Nil"}};
    }
  }
}

function $room_leave_one(_is_a_0, _a_0) {
  if (_is_a_0) {
    return {$: "RStep", "seats": {$: "Empty"}, "accepted": true, "out": {$: "Nil"}};
  } else {
    return {$: "RStep", "seats": {$: "One", "a": _a_0}, "accepted": true, "out": {$: "Nil"}};
  }
}

function $room_leave(_s_0, _id_0) {
  if (_s_0.$ === "Empty") {
    return {$: "RStep", "seats": {$: "Empty"}, "accepted": true, "out": {$: "Nil"}};
  } else if (_s_0.$ === "One") {
    const _a_0 = _s_0["a"];
    return $room_leave_one((_id_0 === _a_0), _a_0);
  } else {
    const _a_1 = _s_0["a"];
    const _b_0 = _s_0["b"];
    return $room_leave_two((_id_0 === _a_1), (_id_0 === _b_0), _a_1, _b_0);
  }
}

function $step(_s_0, _e_0) {
  if (_e_0.$ === "Enter") {
    const _id_0 = _e_0["id"];
    return $room_join(_s_0, _id_0);
  } else if (_e_0.$ === "Talk") {
    const _from_0 = _e_0["from"];
    const _size_0 = _e_0["size"];
    const _text_0 = _e_0["text"];
    const _x_0 = $$MAX();
    return $room_say((_size_0 <= _x_0), _s_0, _from_0, _text_0);
  } else {
    const _id_1 = _e_0["id"];
    return $room_leave(_s_0, _id_1);
  }
}

function $RStep_seats(_t_0) {
  const _s_0 = _t_0["seats"];
  return _s_0;
}

function $RStep_out(_t_0) {
  const _o_0 = _t_0["out"];
  return _o_0;
}

function $after_go($0, $1) {
  for (;;) {
    {
      const _es_0 = $0;
      const _s_0 = $1;
      if (_es_0.$ === "Nil") {
        return _s_0;
      } else {
        const _e_0 = _es_0["head"];
        const _rest_0 = _es_0["tail"];
        $0 = _rest_0;
        $1 = $$RStep_seats($$step(_s_0, _e_0));
        continue;
      }
    }
  }
}

function $after(_es_0) {
  return $after_go(_es_0, {$: "Empty"});
}

function $Seats_distinct(_s_0) {
  if (_s_0.$ === "Two") {
    const _a_0 = _s_0["a"];
    const _b_0 = _s_0["b"];
    return $Bool_not((_a_0 === _b_0));
  } else {
    return true;
  }
}

function $Seats_of(_none_0, _one_0, _a_0, _b_0) {
  if (_none_0) {
    return {$: "Empty"};
  } else {
    if (_one_0) {
      return {$: "One", "a": _a_0};
    } else {
      return {$: "Two", "a": _a_0, "b": _b_0};
    }
  }
}

function $api_seats(_n_0, _a_0, _b_0) {
  return $Seats_of((_n_0 === 0), (_n_0 === 1), _a_0, _b_0);
}

function $api_join(_s_0, _id_0) {
  return $step(_s_0, {$: "Enter", "id": _id_0});
}

function $api_message(_s_0, _from_0, _size_0, _text_0) {
  return $step(_s_0, {$: "Talk", "from": _from_0, "size": _size_0, "text": _text_0});
}

function $api_close(_s_0, _id_0) {
  return $step(_s_0, {$: "Quit", "id": _id_0});
}

function $api_accepted(_t_0) {
  const _t_1 = _t_0["accepted"];
  if (_t_1) {
    return 1;
  } else {
    return 0;
  }
}

function $Notes_len(_ns_0) {
  if (_ns_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ns_0["tail"];
    const _x_0 = $$Notes_len(_t_0);
    return ((1 + _x_0) >>> 0);
  }
}

function $Notes_nth($0, $1) {
  for (;;) {
    {
      const _ns_0 = $0;
      const _n_0 = $1;
      if (_ns_0.$ === "Nil") {
        return {$: "Gone", "to": 0};
      } else {
        const _h_0 = _ns_0["head"];
        const __0 = _ns_0["tail"];
        if (_n_0 == 0) {
          return _h_0;
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = __0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $api_note_count(_t_0) {
  return $Notes_len($$RStep_out(_t_0));
}

function $Note_kind(_n_0) {
  if (_n_0.$ === "Forward") {
    return 0;
  } else if (_n_0.$ === "Joined") {
    return 1;
  } else {
    return 2;
  }
}

function $Note_to(_n_0) {
  if (_n_0.$ === "Forward") {
    const _to_0 = _n_0["to"];
    return _to_0;
  } else if (_n_0.$ === "Joined") {
    const _to_1 = _n_0["to"];
    return _to_1;
  } else {
    const _to_2 = _n_0["to"];
    return _to_2;
  }
}

function $api_note_kind(_t_0, _i_0) {
  return $Note_kind($$Notes_nth($$RStep_out(_t_0), (_i_0 )));
}

function $api_note_to(_t_0, _i_0) {
  return $Note_to($$Notes_nth($$RStep_out(_t_0), (_i_0 )));
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}

const $$room_forward = $room_forward;
const $$MAX = $MAX;
const $$step = $step;
const $$RStep_seats = $RStep_seats;
const $$Notes_len = $Notes_len;
const $$RStep_out = $RStep_out;
const $$Notes_nth = $Notes_nth;export default {
  "MAX": run_lib(() => run_loop($MAX()), 0),
  "room.join.one": run_lib((a0,a1,a2) => run_loop($room_join_one(a0,a1,a2)), 3),
  "room.join": run_lib((a0,a1) => run_loop($room_join(a0,a1)), 2),
  "room.forward.two": run_lib((a0,a1,a2,a3,a4) => run_loop($room_forward_two(a0,a1,a2,a3,str_in(a4))), 5),
  "room.forward": run_lib((a0,a1,a2) => run_loop($room_forward(a0,a1,str_in(a2))), 3),
  "room.say": run_lib((a0,a1,a2,a3) => run_loop($room_say(a0,a1,a2,str_in(a3))), 4),
  "room.leave.two": run_lib((a0,a1,a2,a3) => run_loop($room_leave_two(a0,a1,a2,a3)), 4),
  "room.leave.one": run_lib((a0,a1) => run_loop($room_leave_one(a0,a1)), 2),
  "room.leave": run_lib((a0,a1) => run_loop($room_leave(a0,a1)), 2),
  "step": run_lib((a0,a1) => run_loop($step(a0,a1)), 2),
  "RStep.seats": run_lib((a0) => run_loop($RStep_seats(a0)), 1),
  "RStep.out": run_lib((a0) => run_loop($RStep_out(a0)), 1),
  "after.go": run_lib((a0,a1) => run_loop($after_go(a0,a1)), 2),
  "after": run_lib((a0) => run_loop($after(a0)), 1),
  "Seats.distinct": run_lib((a0) => run_loop($Seats_distinct(a0)), 1),
  "Seats.of": run_lib((a0,a1,a2,a3) => run_loop($Seats_of(a0,a1,a2,a3)), 4),
  "api_seats": run_lib((a0,a1,a2) => run_loop($api_seats(a0,a1,a2)), 3),
  "api_join": run_lib((a0,a1) => run_loop($api_join(a0,a1)), 2),
  "api_message": run_lib((a0,a1,a2,a3) => run_loop($api_message(a0,a1,a2,str_in(a3))), 4),
  "api_close": run_lib((a0,a1) => run_loop($api_close(a0,a1)), 2),
  "api_accepted": run_lib((a0) => run_loop($api_accepted(a0)), 1),
  "Notes.len": run_lib((a0) => run_loop($Notes_len(a0)), 1),
  "Notes.nth": run_lib((a0,a1) => run_loop($Notes_nth(a0,nat_in(a1))), 2),
  "api_note_count": run_lib((a0) => run_loop($api_note_count(a0)), 1),
  "Note.kind": run_lib((a0) => run_loop($Note_kind(a0)), 1),
  "Note.to": run_lib((a0) => run_loop($Note_to(a0)), 1),
  "api_note_kind": run_lib((a0,a1) => run_loop($api_note_kind(a0,a1)), 2),
  "api_note_to": run_lib((a0,a1) => run_loop($api_note_to(a0,a1)), 2),
};
