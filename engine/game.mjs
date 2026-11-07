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

function $W() {
  return 7;
}

function $NONE() {
  return 49;
}

function $sel(_c_0, _a_0, _b_0) {
  if (_c_0) {
    return _a_0;
  } else {
    return _b_0;
  }
}

function $Bool_same(_a_0, _b_0) {
  return $Bool_not((_a_0 !== _b_0));
}

function $rng(_x_0) {
  const _x_1 = (13 >= 32 ? 0 : (_x_0 << 13) >>> 0);
  const _a_0 = ((_x_0 ^ _x_1) >>> 0);
  const _x_2 = (17 >= 32 ? 0 : (_a_0 >>> 17) >>> 0);
  const _b_0 = ((_a_0 ^ _x_2) >>> 0);
  const _x_3 = (5 >= 32 ? 0 : (_b_0 << 5) >>> 0);
  return ((_b_0 ^ _x_3) >>> 0);
}

function $mix(_x_0) {
  const _x_1 = (Math.imul(_x_0, 2654435761) >>> 0);
  return $rng(((_x_1 + 1) >>> 0));
}

function $U32s_has(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_1 = (_h_0 === _x_0);
    const _x_2 = $$U32s_has(_t_0, _x_0);
    return (_x_1 || _x_2);
  }
}

function $U32s_len(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk($$U32s_len(_t_0) + 1);
  }
}

function $U32s_nth($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return 99;
      } else {
        const _h_0 = _xs_0["head"];
        const __0 = _xs_0["tail"];
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

function $U32s_count_add(_hit_0, _n_0) {
  if (_hit_0) {
    return nat_chk(_n_0 + 1);
  } else {
    return _n_0;
  }
}

function $U32s_count(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $U32s_count_add((_h_0 === _x_0), $$U32s_count(_t_0, _x_0));
  }
}

function $U32s_remove_go(_hit_0, _h_0, _t_0, _rest_0) {
  if (_hit_0) {
    return _t_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $U32s_remove(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $U32s_remove_go((_h_0 === _x_0), _h_0, _t_0, $$U32s_remove(_t_0, _x_0));
  }
}

function $U32s_replace_go(_hit_0, _h_0, _t_0, _y_0, _rest_0) {
  if (_hit_0) {
    return {$: "Con", "head": _y_0, "tail": _t_0};
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $U32s_replace(_xs_0, _x_0, _y_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $U32s_replace_go((_h_0 === _x_0), _h_0, _t_0, _y_0, $$U32s_replace(_t_0, _x_0, _y_0));
  }
}

function $U32s_append(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return _ys_0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": _h_0, "tail": $$U32s_append(_t_0, _ys_0)};
  }
}

function $U32s_range(_n_0) {
  if (_n_0 == 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    return $U32s_append($$U32s_range(_p_0), {$: "Con", "head": (_p_0 >>>0), "tail": {$: "Nil"}});
  }
}

function $U32s_sum_mix(_xs_0, _salt_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$mix(((_h_0 + _salt_0) >>> 0));
    const _x_1 = $$U32s_sum_mix(_t_0, _salt_0);
    return ((_x_0 + _x_1) >>> 0);
  }
}

function $Fin7_nat(_f_0) {
  if (_f_0.$ === "F0") {
    return 0;
  } else if (_f_0.$ === "F1") {
    return 1;
  } else if (_f_0.$ === "F2") {
    return 2;
  } else if (_f_0.$ === "F3") {
    return 3;
  } else if (_f_0.$ === "F4") {
    return 4;
  } else if (_f_0.$ === "F5") {
    return 5;
  } else {
    return 6;
  }
}

function $Fin7_of_nat(_n_0) {
  if (_n_0 == 0) {
    return {$: "Some", "value": {$: "F0"}};
  } else if (_n_0 == 1) {
    return {$: "Some", "value": {$: "F1"}};
  } else if (_n_0 == 2) {
    return {$: "Some", "value": {$: "F2"}};
  } else if (_n_0 == 3) {
    return {$: "Some", "value": {$: "F3"}};
  } else if (_n_0 == 4) {
    return {$: "Some", "value": {$: "F4"}};
  } else if (_n_0 == 5) {
    return {$: "Some", "value": {$: "F5"}};
  } else if (_n_0 == 6) {
    return {$: "Some", "value": {$: "F6"}};
  } else {
    return {$: "None"};
  }
}

function $Fin7_down(_ok_0, _n_0, _d_0) {
  if (_ok_0) {
    return $Fin7_of_nat((_n_0 < _d_0 ? 0 : _n_0 - _d_0));
  } else {
    return {$: "None"};
  }
}

function $Fin7_shift(_f_0, _d_0, _plus_0) {
  if (_plus_0) {
    const _x_0 = $$Fin7_nat(_f_0);
    return $Fin7_of_nat(nat_chk(_x_0 + _d_0));
  } else {
    return $Fin7_down($$Nat_is_le(_d_0, $$Fin7_nat(_f_0)), $$Fin7_nat(_f_0), _d_0);
  }
}

function $Cell_eq(_a_0, _b_0) {
  const _ac_0 = _a_0["col"];
  const _ar_0 = _a_0["row"];
  const _bc_0 = _b_0["col"];
  const _br_0 = _b_0["row"];
  return $Bool_and($$Nat_is_eq($$Fin7_nat(_ac_0), $$Fin7_nat(_bc_0)), $$Nat_is_eq($$Fin7_nat(_ar_0), $$Fin7_nat(_br_0)));
}

function $Cell_sel(_c_0, _a_0, _b_0) {
  if (_c_0) {
    return _a_0;
  } else {
    return _b_0;
  }
}

function $Cell_is(_m_0, _c_0) {
  if (_m_0.$ === "Some") {
    const _x_0 = _m_0["value"];
    return $Cell_eq(_x_0, _c_0);
  } else {
    return false;
  }
}

function $Cell_none(_m_0) {
  if (_m_0.$ === "Some") {
    return false;
  } else {
    return true;
  }
}

function $Cell_both(_c_0, _r_0) {
  if (_c_0.$ === "Some") {
    const _x_0 = _c_0["value"];
    if (_r_0.$ === "Some") {
      const _y_0 = _r_0["value"];
      return {$: "Some", "value": {$: "Cell", "col": _x_0, "row": _y_0}};
    } else {
      return {$: "None"};
    }
  } else {
    return {$: "None"};
  }
}

function $Cell_u32(_c_0) {
  const _col_0 = _c_0["col"];
  const _row_0 = _c_0["row"];
  const _x_0 = $$Fin7_nat(_row_0);
  const _x_1 = (_x_0 >>>0);
  const _x_2 = $$Fin7_nat(_col_0);
  const _x_3 = (Math.imul(_x_1, 7) >>> 0);
  const _x_4 = (_x_2 >>>0);
  return ((_x_3 + _x_4) >>> 0);
}

function $Cell_of_u32(_x_0) {
  const _x_1 = (7 === 0 ? _x_0 : _x_0 % 7);
  const _x_2 = (7 === 0 ? 0 : (_x_0 / 7) >>> 0);
  return $Cell_both($$Fin7_of_nat((_x_1 )), $$Fin7_of_nat((_x_2 )));
}

function $Cell_or_corner(_m_0) {
  if (_m_0.$ === "Some") {
    const _c_0 = _m_0["value"];
    return _c_0;
  } else {
    return {$: "Cell", "col": {$: "F0"}, "row": {$: "F0"}};
  }
}

function $Cell_code(_m_0) {
  if (_m_0.$ === "Some") {
    const _c_0 = _m_0["value"];
    return $Cell_u32(_c_0);
  } else {
    return $NONE();
  }
}

function $Fin7s_all() {
  return {$: "Con", "head": {$: "F0"}, "tail": {$: "Con", "head": {$: "F1"}, "tail": {$: "Con", "head": {$: "F2"}, "tail": {$: "Con", "head": {$: "F3"}, "tail": {$: "Con", "head": {$: "F4"}, "tail": {$: "Con", "head": {$: "F5"}, "tail": {$: "Con", "head": {$: "F6"}, "tail": {$: "Nil"}}}}}}}};
}

function $Cells_row(_cs_0, _r_0, _rest_0) {
  if (_cs_0.$ === "Nil") {
    return _rest_0;
  } else {
    const _c_0 = _cs_0["head"];
    const _t_0 = _cs_0["tail"];
    return {$: "Con", "head": {$: "Cell", "col": _c_0, "row": _r_0}, "tail": $$Cells_row(_t_0, _r_0, _rest_0)};
  }
}

function $Cells_rows(_rs_0) {
  if (_rs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _r_0 = _rs_0["head"];
    const _t_0 = _rs_0["tail"];
    return $Cells_row($$Fin7s_all(), _r_0, $$Cells_rows(_t_0));
  }
}

function $Cells_all() {
  return $Cells_rows($$Fin7s_all());
}

function $Cells_has(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_1 = $$Cell_eq(_h_0, _x_0);
    const _x_2 = $$Cells_has(_t_0, _x_0);
    return (_x_1 || _x_2);
  }
}

function $Cells_len(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk($$Cells_len(_t_0) + 1);
  }
}

function $Cells_take(_n_0, _xs_0) {
  if (_n_0 == 0) {
    if (_xs_0.$ === "Nil") {
      return {$: "Nil"};
    } else {
      return {$: "Nil"};
    }
  } else {
    const _p_0 = (_n_0 - 1);
    if (_xs_0.$ === "Nil") {
      return {$: "Nil"};
    } else {
      const _h_0 = _xs_0["head"];
      const _t_0 = _xs_0["tail"];
      return {$: "Con", "head": _h_0, "tail": $$Cells_take(_p_0, _t_0)};
    }
  }
}

function $Cells_append(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return _ys_0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": _h_0, "tail": $$Cells_append(_t_0, _ys_0)};
  }
}

function $Side_other(_s_0) {
  if (_s_0.$ === "Blue") {
    return {$: "Red"};
  } else {
    return {$: "Blue"};
  }
}

function $Side_is_blue(_s_0) {
  if (_s_0.$ === "Blue") {
    return true;
  } else {
    return false;
  }
}

function $Side_of_bool(_blue_0) {
  if (_blue_0) {
    return {$: "Blue"};
  } else {
    return {$: "Red"};
  }
}

function $Side_of_code(_c_0) {
  return $Side_of_bool((_c_0 === 0));
}

function $Side_same(_a_0, _b_0) {
  return $Bool_same($$Side_is_blue(_a_0), $$Side_is_blue(_b_0));
}

function $Side_code(_s_0) {
  return $sel($$Side_is_blue(_s_0), 0, 1);
}

function $Side_home(_s_0) {
  if (_s_0.$ === "Blue") {
    return {$: "Cell", "col": {$: "F3"}, "row": {$: "F6"}};
  } else {
    return {$: "Cell", "col": {$: "F3"}, "row": {$: "F0"}};
  }
}

function $Step_mirror(_s_0) {
  const _r_0 = _s_0["right"];
  const _dx_0 = _s_0["dx"];
  const _u_0 = _s_0["up"];
  const _dy_0 = _s_0["dy"];
  return {$: "Step", "right": $$Bool_not(_r_0), "dx": _dx_0, "up": _u_0, "dy": _dy_0};
}

function $Step_flip(_s_0) {
  const _r_0 = _s_0["right"];
  const _dx_0 = _s_0["dx"];
  const _u_0 = _s_0["up"];
  const _dy_0 = _s_0["dy"];
  return {$: "Step", "right": _r_0, "dx": _dx_0, "up": $$Bool_not(_u_0), "dy": _dy_0};
}

function $Step_is_vertical(_s_0) {
  const _dx_0 = _s_0["dx"];
  return $Nat_is_eq(_dx_0, 0);
}

function $Step_same(_a_0, _b_0) {
  const _ar_0 = _a_0["right"];
  const _adx_0 = _a_0["dx"];
  const _au_0 = _a_0["up"];
  const _ady_0 = _a_0["dy"];
  const _br_0 = _b_0["right"];
  const _bdx_0 = _b_0["dx"];
  const _bu_0 = _b_0["up"];
  const _bdy_0 = _b_0["dy"];
  const _x_0 = $$Nat_is_eq(_adx_0, 0);
  const _x_1 = $$Bool_same(_ar_0, _br_0);
  const _x_2 = $$Nat_is_eq(_ady_0, 0);
  const _x_3 = $$Bool_same(_au_0, _bu_0);
  return $Bool_and($$Bool_and($$Bool_and($$Nat_is_eq(_adx_0, _bdx_0), $$Nat_is_eq(_ady_0, _bdy_0)), (_x_0 || _x_1)), (_x_2 || _x_3));
}

function $Step_reach(_s_0) {
  const _dx_0 = _s_0["dx"];
  const _dy_0 = _s_0["dy"];
  return (_dx_0 > _dy_0 ? _dx_0 : _dy_0);
}

function $Step_target(_st_0, _sq_0, _side_0) {
  const _r_0 = _st_0["right"];
  const _dx_0 = _st_0["dx"];
  const _u_0 = _st_0["up"];
  const _dy_0 = _st_0["dy"];
  const _c_0 = _sq_0["col"];
  const _w_0 = _sq_0["row"];
  const _red_0 = $$Bool_not($$Side_is_blue(_side_0));
  return $Cell_both($$Fin7_shift(_c_0, _dx_0, (_r_0 !== _red_0)), $$Fin7_shift(_w_0, _dy_0, $$Bool_not((_u_0 !== _red_0))));
}

function $Dist_nat(_d_0) {
  if (_d_0.$ === "Sq1") {
    return 1;
  } else if (_d_0.$ === "Sq2") {
    return 2;
  } else {
    return 3;
  }
}

function $Shape_steps(_sh_0, _rest_0) {
  if (_sh_0.$ === "Sideways") {
    const _d_0 = _sh_0["dx"];
    const _u_0 = _sh_0["up"];
    const _dy_0 = _sh_0["dy"];
    return {$: "Con", "head": {$: "Step", "right": false, "dx": $$Dist_nat(_d_0), "up": _u_0, "dy": _dy_0}, "tail": {$: "Con", "head": {$: "Step", "right": true, "dx": $$Dist_nat(_d_0), "up": _u_0, "dy": _dy_0}, "tail": _rest_0}};
  } else {
    const _d_1 = _sh_0["dy"];
    return {$: "Con", "head": {$: "Step", "right": true, "dx": 0, "up": false, "dy": $$Dist_nat(_d_1)}, "tail": {$: "Con", "head": {$: "Step", "right": true, "dx": 0, "up": true, "dy": $$Dist_nat(_d_1)}, "tail": _rest_0}};
  }
}

function $Shapes_steps(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Shape_steps(_h_0, $$Shapes_steps(_t_0));
  }
}

function $Card_make(_d_0) {
  const _i_0 = _d_0["id"];
  const _n_0 = _d_0["name"];
  const _sh_0 = _d_0["shapes"];
  return {$: "Card", "id": _i_0, "name": _n_0, "steps": $$Shapes_steps(_sh_0)};
}

function $deck_defs() {
  return {$: "Con", "head": {$: "CardDef", "id": 0, "name": "Toque", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 1, "name": "Tabela", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 1}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 1}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 2, "name": "Abertura", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 3, "name": "Triangulação", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 1}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 4, "name": "Lançamento", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq2"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 5, "name": "Chutão", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq3"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 6, "name": "Drible", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 2}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 2}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 7, "name": "Chapéu", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": false, "dy": 1}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": true, "dy": 1}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 8, "name": "Pelada", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 1}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 9, "name": "Cruzamento", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": true, "dy": 1}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 10, "name": "Enfiada", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 1}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq2"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 11, "name": "Bicicleta", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": false, "dy": 2}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq2"}, "up": true, "dy": 2}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Nil"}}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 12, "name": "Inversão", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq3"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 13, "name": "Recuo", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 1}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 14, "name": "Marcação", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 1}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 0}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq2"}}, "tail": {$: "Nil"}}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 15, "name": "Retranca", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 2}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 16, "name": "Arrancada", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 2}, "tail": {$: "Con", "head": {$: "Straight", "dy": {$: "Sq1"}}, "tail": {$: "Nil"}}}}, "tail": {$: "Con", "head": {$: "CardDef", "id": 17, "name": "Contra-ataque", "shapes": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq3"}, "up": true, "dy": 3}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": false, "dy": 1}, "tail": {$: "Con", "head": {$: "Sideways", "dx": {$: "Sq1"}, "up": true, "dy": 1}, "tail": {$: "Nil"}}}}}, "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}};
}

function $CardDefs_make(_ds_0) {
  if (_ds_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _d_0 = _ds_0["head"];
    const _t_0 = _ds_0["tail"];
    return {$: "Con", "head": $$Card_make(_d_0), "tail": $$CardDefs_make(_t_0)};
  }
}

function $CardDefs_nth($0, $1) {
  for (;;) {
    {
      const _ds_0 = $0;
      const _n_0 = $1;
      if (_ds_0.$ === "Nil") {
        return {$: "CardDef", "id": 99, "name": "", "shapes": {$: "Nil"}};
      } else {
        const _h_0 = _ds_0["head"];
        const __0 = _ds_0["tail"];
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

function $deck() {
  return $CardDefs_make($$deck_defs());
}

function $Steps_has(_xs_0, _s_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$Step_same(_h_0, _s_0);
    const _x_1 = $$Steps_has(_t_0, _s_0);
    return (_x_0 || _x_1);
  }
}

function $Steps_max_reach(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$Step_reach(_h_0);
    const _x_1 = $$Steps_max_reach(_t_0);
    return (_x_0 > _x_1 ? _x_0 : _x_1);
  }
}

function $Cards_ids(_cs_0) {
  if (_cs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _cs_0["head"];
    const _i_0 = _t_0["id"];
    const _t_1 = _cs_0["tail"];
    return {$: "Con", "head": _i_0, "tail": $$Cards_ids(_t_1)};
  }
}

function $Cards_len(_cs_0) {
  if (_cs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _cs_0["tail"];
    return nat_chk($$Cards_len(_t_0) + 1);
  }
}

function $Cards_max_reach(_cs_0) {
  if (_cs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _cs_0["head"];
    const _st_0 = _t_0["steps"];
    const _t_1 = _cs_0["tail"];
    const _x_0 = $$Steps_max_reach(_st_0);
    const _x_1 = $$Cards_max_reach(_t_1);
    return (_x_0 > _x_1 ? _x_0 : _x_1);
  }
}

function $Cards_steps_of_pick(_hit_0, _a_0, _b_0) {
  if (_hit_0) {
    return _a_0;
  } else {
    return _b_0;
  }
}

function $Cards_steps_of(_cs_0, _id_0) {
  if (_cs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _cs_0["head"];
    const _cid_0 = _t_0["id"];
    const _st_0 = _t_0["steps"];
    const _t_1 = _cs_0["tail"];
    return $Cards_steps_of_pick((_cid_0 === _id_0), _st_0, $$Cards_steps_of(_t_1, _id_0));
  }
}

function $Steps_len(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk($$Steps_len(_t_0) + 1);
  }
}

function $Steps_nth($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return {$: "Step", "right": true, "dx": 0, "up": true, "dy": 0};
      } else {
        const _h_0 = _xs_0["head"];
        const __0 = _xs_0["tail"];
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

function $Step_pack(_s_0) {
  const _r_0 = _s_0["right"];
  const _dx_0 = _s_0["dx"];
  const _u_0 = _s_0["up"];
  const _dy_0 = _s_0["dy"];
  const _x_0 = (_dx_0 >>>0);
  const _y_0 = (_dy_0 >>>0);
  const _x_1 = $$sel(_r_0, ((3 + _x_0) >>> 0), ((3 - _x_0) >>> 0));
  const _x_2 = (Math.imul(_x_1, 8) >>> 0);
  const _x_3 = $$sel(_u_0, ((3 + _y_0) >>> 0), ((3 - _y_0) >>> 0));
  return ((_x_2 + _x_3) >>> 0);
}

function $deck_size() {
  return $Cards_len($$deck());
}

function $deck_card(_i_0) {
  return $Card_make($$CardDefs_nth($$deck_defs(), _i_0));
}

function $deck_max_step() {
  return $Cards_max_reach($$deck());
}

function $card_has(_c_0, _s_0) {
  const _st_0 = _c_0["steps"];
  return $Steps_has(_st_0, _s_0);
}

function $card_steps(_id_0) {
  return $Cards_steps_of($$deck(), _id_0);
}

function $Deal_hand_of(_d_0, _s_0) {
  const _b_0 = _d_0["blue"];
  const __0 = _d_0["red"];
  if (_s_0.$ === "Blue") {
    return _b_0;
  } else {
    return __0;
  }
}

function $U32s_nth_or($0, $1, $2) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      const _d_0 = $2;
      if (_xs_0.$ === "Nil") {
        return _d_0;
      } else {
        const _h_0 = _xs_0["head"];
        const __0 = _xs_0["tail"];
        if (_n_0 == 0) {
          return _h_0;
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = __0;
          $1 = _p_0;
          $2 = _d_0;
          continue;
        }
      }
    }
  }
}

function $draw_pick(_xs_0, _r_0) {
  const _x_0 = $$U32s_len(_xs_0);
  const _x_1 = (_x_0 >>>0);
  const _x_2 = (_x_1 === 0 ? _r_0 : _r_0 % _x_1);
  return $U32s_nth_or(_xs_0, (_x_2 ), 0);
}

function $draw_n(_n_0, _xs_0, _r_0) {
  if (_n_0 == 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    const _c_0 = $$draw_pick(_xs_0, _r_0);
    return {$: "Con", "head": _c_0, "tail": $$draw_n(_p_0, $$U32s_remove(_xs_0, _c_0), $$rng(_r_0))};
  }
}

function $Deal_of_list(_cs_0) {
  if (_cs_0.$ === "Con") {
    const _a_0 = _cs_0["head"];
    const _t_0 = _cs_0["tail"];
    if (_t_0.$ === "Con") {
      const _b_0 = _t_0["head"];
      const _t_1 = _t_0["tail"];
      if (_t_1.$ === "Con") {
        const _c_0 = _t_1["head"];
        const _t_2 = _t_1["tail"];
        if (_t_2.$ === "Con") {
          const _d_0 = _t_2["head"];
          const _t_3 = _t_2["tail"];
          if (_t_3.$ === "Con") {
            const _e_0 = _t_3["head"];
            return {$: "Deal", "blue": {$: "Con", "head": _a_0, "tail": {$: "Con", "head": _b_0, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": _c_0, "tail": {$: "Con", "head": _d_0, "tail": {$: "Nil"}}}, "table": _e_0};
          } else {
            return {$: "Deal", "blue": {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}}, "table": 4};
          }
        } else {
          return {$: "Deal", "blue": {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}}, "table": 4};
        }
      } else {
        return {$: "Deal", "blue": {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}}, "table": 4};
      }
    } else {
      return {$: "Deal", "blue": {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}}, "table": 4};
    }
  } else {
    return {$: "Deal", "blue": {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}}, "table": 4};
  }
}

function $Nats_head0(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    return _h_0;
  }
}

function $Nats_tail(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _xs_0["tail"];
    return _t_0;
  }
}

function $U32s_rot1(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $U32s_append(_t_0, {$: "Con", "head": _h_0, "tail": {$: "Nil"}});
  }
}

function $U32s_rotate($0, $1) {
  for (;;) {
    {
      const _k_0 = $0;
      const _xs_0 = $1;
      if (_k_0 == 0) {
        return _xs_0;
      } else {
        const _p_0 = (_k_0 - 1);
        $0 = _p_0;
        $1 = $$U32s_rot1(_xs_0);
        continue;
      }
    }
  }
}

function $Draw_k(_bs_0, _rs_0) {
  const _x_0 = $$Nats_head0(_bs_0);
  const _x_1 = $$Nats_head0(_rs_0);
  return nat_chk(_x_0 + _x_1);
}

function $Draw_go(_n_0, _rot_0, _bs_0, _rs_0) {
  if (_n_0 == 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    if (_rot_0.$ === "Nil") {
      return {$: "Nil"};
    } else {
      const _c_0 = _rot_0["head"];
      const _rest_0 = _rot_0["tail"];
      return {$: "Con", "head": _c_0, "tail": $$Draw_go(_p_0, $$U32s_rotate($$Draw_k($$Nats_tail(_bs_0), $$Nats_tail(_rs_0)), _rest_0), $$Nats_tail(_bs_0), $$Nats_tail(_rs_0))};
    }
  }
}

function $deal_from(_blue_0, _red_0) {
  const _bs_0 = _blue_0["picks"];
  const _rs_0 = _red_0["picks"];
  return $Deal_of_list($$Draw_go(5, $$U32s_rotate($$Draw_k(_bs_0, _rs_0), $$Cards_ids($$deck())), _bs_0, _rs_0));
}

function $Secret_of_key(_k_0) {
  const _k1_0 = $$rng(_k_0);
  const _k2_0 = $$rng(_k1_0);
  const _k3_0 = $$rng(_k2_0);
  const _k4_0 = $$rng(_k3_0);
  const _k5_0 = $$rng(_k4_0);
  const _x_0 = (18 === 0 ? _k_0 : _k_0 % 18);
  const _x_1 = (18 === 0 ? _k1_0 : _k1_0 % 18);
  const _x_2 = (18 === 0 ? _k2_0 : _k2_0 % 18);
  const _x_3 = (18 === 0 ? _k3_0 : _k3_0 % 18);
  const _x_4 = (18 === 0 ? _k4_0 : _k4_0 % 18);
  return {$: "Secret", "coin": $$U32_is_even(_k5_0), "picks": {$: "Con", "head": (_x_0 ), "tail": {$: "Con", "head": (_x_1 ), "tail": {$: "Con", "head": (_x_2 ), "tail": {$: "Con", "head": (_x_3 ), "tail": {$: "Con", "head": (_x_4 ), "tail": {$: "Nil"}}}}}}};
}

function $U32s_distinct(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Bool_and($$Bool_not($$U32s_has(_t_0, _h_0)), $$U32s_distinct(_t_0));
  }
}

function $U32s_all_in(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Bool_and($$U32s_has(_ys_0, _h_0), $$U32s_all_in(_t_0, _ys_0));
  }
}

function $Deal_five_ok(_xs_0) {
  return $Bool_and($$U32s_distinct(_xs_0), $$U32s_all_in(_xs_0, $$Cards_ids($$deck())));
}

function $Deal_is_valid(_d_0) {
  const _t_0 = _d_0["blue"];
  if (_t_0.$ === "Con") {
    const _a_0 = _t_0["head"];
    const _t_1 = _t_0["tail"];
    if (_t_1.$ === "Con") {
      const _b_0 = _t_1["head"];
      const _t_2 = _t_1["tail"];
      if (_t_2.$ === "Nil") {
        const _t_3 = _d_0["red"];
        if (_t_3.$ === "Con") {
          const _c_0 = _t_3["head"];
          const _t_4 = _t_3["tail"];
          if (_t_4.$ === "Con") {
            const _e_0 = _t_4["head"];
            const _t_5 = _t_4["tail"];
            if (_t_5.$ === "Nil") {
              const _t_6 = _d_0["table"];
              return $Deal_five_ok({$: "Con", "head": _a_0, "tail": {$: "Con", "head": _b_0, "tail": {$: "Con", "head": _c_0, "tail": {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _t_6, "tail": {$: "Nil"}}}}}});
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    return false;
  }
}

function $Setup_deal(_s_0) {
  const _b_0 = _s_0["blue_secret"];
  const _r_0 = _s_0["red_secret"];
  return $deal_from(_b_0, _r_0);
}

function $Coin_side(_blue_0, _red_0) {
  return $Side_of_bool($$Bool_same(_blue_0, _red_0));
}

function $Setup_starter(_s_0) {
  const _t_0 = _s_0["blue_secret"];
  const _bc_0 = _t_0["coin"];
  const _t_1 = _s_0["red_secret"];
  const _rc_0 = _t_1["coin"];
  return $Coin_side(_bc_0, _rc_0);
}

function $Piece_code(_side_0, _teacher_0) {
  const _x_0 = $$sel($$Side_is_blue(_side_0), 1, 3);
  const _x_1 = $$sel(_teacher_0, 1, 0);
  return ((_x_0 + _x_1) >>> 0);
}

function $Pieces_code_at(_ps_0, _sq_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    return $sel($$Cell_eq(_q_0, _sq_0), $$Piece_code(_s_0, _t_1), $$Pieces_code_at(_rest_0, _sq_0));
  }
}

function $Code_is_side(_c_0, _side_0) {
  if (_side_0.$ === "Blue") {
    const _x_0 = (_c_0 === 1);
    const _x_1 = (_c_0 === 2);
    return (_x_0 || _x_1);
  } else {
    const _x_2 = (_c_0 === 3);
    const _x_3 = (_c_0 === 4);
    return (_x_2 || _x_3);
  }
}

function $Pieces_side_at(_ps_0, _sq_0, _side_0) {
  return $Code_is_side($$Pieces_code_at(_ps_0, _sq_0), _side_0);
}

function $Pieces_teacher_of_pick(_hit_0, _q_0, _rest_0) {
  if (_hit_0) {
    return {$: "Some", "value": _q_0};
  } else {
    return _rest_0;
  }
}

function $Pieces_teacher_of(_ps_0, _side_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    return $Pieces_teacher_of_pick($$Bool_and($$Side_same(_s_0, _side_0), _t_1), _q_0, $$Pieces_teacher_of(_rest_0, _side_0));
  }
}

function $Pieces_len(_ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ps_0["tail"];
    return nat_chk($$Pieces_len(_t_0) + 1);
  }
}

function $Pieces_capture_go(_hit_0, _p_0, _rest_0) {
  if (_hit_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _p_0, "tail": _rest_0};
  }
}

function $Pieces_capture(_ps_0, _sq_0, _enemy_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    return $Pieces_capture_go($$Bool_and($$Side_same(_s_0, _enemy_0), $$Cell_eq(_q_0, _sq_0)), {$: "Piece", "side": _s_0, "teacher": _t_1, "square": _q_0}, $$Pieces_capture(_rest_0, _sq_0, _enemy_0));
  }
}

function $Pieces_move(_ps_0, _from_0, _to_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    return {$: "Con", "head": {$: "Piece", "side": _s_0, "teacher": _t_1, "square": $$Cell_sel($$Cell_eq(_q_0, _from_0), _to_0, _q_0)}, "tail": $$Pieces_move(_rest_0, _from_0, _to_0)};
  }
}

function $Pieces_key(_ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    const _x_0 = $$Piece_code(_s_0, _t_1);
    const _x_1 = (Math.imul(_x_0, 64) >>> 0);
    const _x_2 = $$Cell_u32(_q_0);
    const _x_3 = $$mix(((_x_1 + _x_2) >>> 0));
    const _x_4 = $$Pieces_key(_rest_0);
    return ((_x_3 + _x_4) >>> 0);
  }
}

function $Pieces_start() {
  return {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F0"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F1"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F2"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": true, "square": {$: "Cell", "col": {$: "F3"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F4"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F5"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Blue"}, "teacher": false, "square": {$: "Cell", "col": {$: "F6"}, "row": {$: "F6"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F0"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F1"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F2"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": true, "square": {$: "Cell", "col": {$: "F3"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F4"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F5"}, "row": {$: "F0"}}}, "tail": {$: "Con", "head": {$: "Piece", "side": {$: "Red"}, "teacher": false, "square": {$: "Cell", "col": {$: "F6"}, "row": {$: "F0"}}}, "tail": {$: "Nil"}}}}}}}}}}}}}}};
}

function $Outcome_is_win(_o_0) {
  if (_o_0.$ === "Winner") {
    return true;
  } else {
    return false;
  }
}

function $Outcome_is_over(_o_0) {
  if (_o_0.$ === "Ongoing") {
    return false;
  } else {
    return true;
  }
}

function $Outcome_code(_o_0) {
  if (_o_0.$ === "Ongoing") {
    return 0;
  } else if (_o_0.$ === "Winner") {
    const _s_0 = _o_0["side"];
    return $sel($$Side_is_blue(_s_0), 1, 2);
  } else {
    return 3;
  }
}

function $Action_card(_m_0) {
  const _c_0 = _m_0["card"];
  return _c_0;
}

function $Action_from(_m_0) {
  const _f_0 = _m_0["from"];
  return _f_0;
}

function $to_of(_m_0) {
  const _t_0 = _m_0["to"];
  return _t_0;
}

function $Action_same(_a_0, _b_0) {
  const _c1_0 = _a_0["card"];
  const _f1_0 = _a_0["from"];
  const _t1_0 = _a_0["to"];
  const _c2_0 = _b_0["card"];
  const _f2_0 = _b_0["from"];
  const _t2_0 = _b_0["to"];
  return $Bool_and($$Bool_and((_c1_0 === _c2_0), $$Cell_eq(_f1_0, _f2_0)), $$Cell_eq(_t1_0, _t2_0));
}

function $Action_code(_m_0) {
  const _c_0 = _m_0["card"];
  const _f_0 = _m_0["from"];
  const _t_0 = _m_0["to"];
  const _x_0 = $$Cell_u32(_f_0);
  const _x_1 = (Math.imul(_c_0, 2401) >>> 0);
  const _x_2 = (Math.imul(_x_0, 49) >>> 0);
  const _x_3 = ((_x_1 + _x_2) >>> 0);
  const _x_4 = $$Cell_u32(_t_0);
  return ((_x_3 + _x_4) >>> 0);
}

function $Action_of_code(_n_0) {
  const _x_0 = (49 === 0 ? 0 : (_n_0 / 49) >>> 0);
  return {$: "Action", "card": (2401 === 0 ? 0 : (_n_0 / 2401) >>> 0), "from": $$Cell_or_corner($$Cell_of_u32((49 === 0 ? _x_0 : _x_0 % 49))), "to": $$Cell_or_corner($$Cell_of_u32((49 === 0 ? _n_0 : _n_0 % 49)))};
}

function $Action_valid_code(_n_0) {
  const _x_0 = $$Action_code($$Action_of_code(_n_0));
  return (_x_0 === _n_0);
}

function $Actions_has(_xs_0, _m_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$Action_same(_h_0, _m_0);
    const _x_1 = $$Actions_has(_t_0, _m_0);
    return (_x_0 || _x_1);
  }
}

function $Actions_nonempty(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    return true;
  }
}

function $Actions_len(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk($$Actions_len(_t_0) + 1);
  }
}

function $Actions_nth($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return {$: "Action", "card": 99, "from": {$: "Cell", "col": {$: "F0"}, "row": {$: "F0"}}, "to": {$: "Cell", "col": {$: "F0"}, "row": {$: "F0"}}};
      } else {
        const _h_0 = _xs_0["head"];
        const __0 = _xs_0["tail"];
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

function $Game_turn(_g_0) {
  const _t_0 = _g_0["turn"];
  return _t_0;
}

function $Game_pieces(_g_0) {
  const _p_0 = _g_0["pieces"];
  return _p_0;
}

function $Game_result(_g_0) {
  const _r_0 = _g_0["result"];
  return _r_0;
}

function $Game_hand(_g_0, _s_0) {
  const _b_0 = _g_0["blue"];
  const __2 = _g_0["red"];
  if (_s_0.$ === "Blue") {
    return _b_0;
  } else {
    return __2;
  }
}

function $Game_table(_g_0) {
  const _t_0 = _g_0["table"];
  return _t_0;
}

function $Game_quiet(_g_0) {
  const _q_0 = _g_0["quiet"];
  return _q_0;
}

function $Game_history(_g_0) {
  const _h_0 = _g_0["history"];
  return _h_0;
}

function $Game_key(_ps_0, _b_0, _r_0, _t_0, _turn_0) {
  const _x_0 = $$Pieces_key(_ps_0);
  const _x_1 = $$U32s_sum_mix(_b_0, 100);
  const _x_2 = ((_x_0 + _x_1) >>> 0);
  const _x_3 = $$U32s_sum_mix(_r_0, 200);
  const _x_4 = ((_x_2 + _x_3) >>> 0);
  const _x_5 = $$mix(((_t_0 + 300) >>> 0));
  const _x_6 = ((_x_4 + _x_5) >>> 0);
  const _x_7 = $$sel($$Side_is_blue(_turn_0), 0, 977);
  return ((_x_6 + _x_7) >>> 0);
}

function $start_dealt(_starter_0, _d_0) {
  const _b_0 = _d_0["blue"];
  const _r_0 = _d_0["red"];
  const _t_0 = _d_0["table"];
  return {$: "Game", "turn": _starter_0, "pieces": $$Pieces_start(), "blue": _b_0, "red": _r_0, "table": _t_0, "quiet": 0, "history": {$: "Con", "head": $$Game_key($$Pieces_start(), _b_0, _r_0, _t_0, _starter_0), "tail": {$: "Nil"}}, "result": {$: "Ongoing"}};
}

function $start(_setup_0) {
  return $start_dealt($$Setup_starter(_setup_0), $$Setup_deal(_setup_0));
}

function $gen_add(_skip_0, _m_0, _acc_0) {
  if (_skip_0) {
    return _acc_0;
  } else {
    return {$: "Con", "head": _m_0, "tail": _acc_0};
  }
}

function $gen_add_to(_t_0, _card_0, _from_0, _side_0, _ps_0, _acc_0) {
  if (_t_0.$ === "None") {
    return _acc_0;
  } else {
    const _to_0 = _t_0["value"];
    return $gen_add($$Pieces_side_at(_ps_0, _to_0, _side_0), {$: "Action", "card": _card_0, "from": _from_0, "to": _to_0}, _acc_0);
  }
}

function $gen_steps($0, $1, $2, $3, $4, $5) {
  for (;;) {
    {
      const _sts_0 = $0;
      const _card_0 = $1;
      const _from_0 = $2;
      const _side_0 = $3;
      const _ps_0 = $4;
      const _acc_0 = $5;
      if (_sts_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _st_0 = _sts_0["head"];
        const _rest_0 = _sts_0["tail"];
        $0 = _rest_0;
        $1 = _card_0;
        $2 = _from_0;
        $3 = _side_0;
        $4 = _ps_0;
        $5 = $$gen_add_to($$Step_target(_st_0, _from_0, _side_0), _card_0, _from_0, _side_0, _ps_0, _acc_0);
        continue;
      }
    }
  }
}

function $gen_pieces_one(_mine_0, _sts_0, _card_0, _q_0, _side_0, _ps_0, _acc_0) {
  if (_mine_0) {
    return $gen_steps(_sts_0, _card_0, _q_0, _side_0, _ps_0, _acc_0);
  } else {
    return _acc_0;
  }
}

function $gen_pieces($0, $1, $2, $3, $4, $5) {
  for (;;) {
    {
      const _it_0 = $0;
      const _card_0 = $1;
      const _sts_0 = $2;
      const _side_0 = $3;
      const _ps_0 = $4;
      const _acc_0 = $5;
      if (_it_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _t_0 = _it_0["head"];
        const _s_0 = _t_0["side"];
        const _q_0 = _t_0["square"];
        const _rest_0 = _it_0["tail"];
        $0 = _rest_0;
        $1 = _card_0;
        $2 = _sts_0;
        $3 = _side_0;
        $4 = _ps_0;
        $5 = $$gen_pieces_one($$Side_same(_s_0, _side_0), _sts_0, _card_0, _q_0, _side_0, _ps_0, _acc_0);
        continue;
      }
    }
  }
}

function $gen_cards($0, $1, $2, $3) {
  for (;;) {
    {
      const _hand_0 = $0;
      const _side_0 = $1;
      const _ps_0 = $2;
      const _acc_0 = $3;
      if (_hand_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _c_0 = _hand_0["head"];
        const _rest_0 = _hand_0["tail"];
        $0 = _rest_0;
        $1 = _side_0;
        $2 = _ps_0;
        $3 = $$gen_pieces(_ps_0, _c_0, $$card_steps(_c_0), _side_0, _ps_0, _acc_0);
        continue;
      }
    }
  }
}

function $gen_if_ongoing(_over_0, _g_0) {
  if (_over_0) {
    return {$: "Nil"};
  } else {
    return $gen_cards($$Game_hand(_g_0, $$Game_turn(_g_0)), $$Game_turn(_g_0), $$Game_pieces(_g_0), {$: "Nil"});
  }
}

function $legal_moves(_g_0) {
  return $gen_if_ongoing($$Outcome_is_over($$Game_result(_g_0)), _g_0);
}

function $is_legal(_g_0, _m_0) {
  return $Actions_has($$legal_moves(_g_0), _m_0);
}

function $card_proven(_g_0, _m_0) {
  const _c_0 = _m_0["card"];
  return $U32s_has($$Game_hand(_g_0, $$Game_turn(_g_0)), _c_0);
}

function $outcome_after(_win_0, _mover_0, _draw_0) {
  if (_win_0) {
    return {$: "Winner", "side": _mover_0};
  } else {
    if (_draw_0) {
      return {$: "Draw"};
    } else {
      return {$: "Ongoing"};
    }
  }
}

function $hand_after(_mine_0, _h_0, _card_0, _table_0) {
  if (_mine_0) {
    return $U32s_replace(_h_0, _card_0, _table_0);
  } else {
    return _h_0;
  }
}

function $history_after(_captured_0, _key_0, _h_0) {
  if (_captured_0) {
    return {$: "Con", "head": _key_0, "tail": {$: "Nil"}};
  } else {
    return {$: "Con", "head": _key_0, "tail": _h_0};
  }
}

function $quiet_after(_captured_0, _q_0) {
  if (_captured_0) {
    return 0;
  } else {
    return nat_chk(_q_0 + 1);
  }
}

function $Game_drawn(_h_0, _q_0) {
  const _x_0 = $$Nat_is_ge($$U32s_count(_h_0, $$U32s_nth(_h_0, 0)), 3);
  const _x_1 = $$Nat_is_ge(_q_0, 20);
  return (_x_0 || _x_1);
}

function $won(_ps_0, _enemy_0, _to_0) {
  const _x_0 = $$Cell_is($$Pieces_teacher_of(_ps_0, _enemy_0), _to_0);
  const _x_1 = $$Cell_eq(_to_0, $$Side_home(_enemy_0));
  return (_x_0 || _x_1);
}

function $apply_go(_win_0, _turn_0, _ps_0, _b_0, _r_0, _table_0, _q_0, _h_0, _card_0, _from_0, _to_0) {
  const _enemy_0 = $$Side_other(_turn_0);
  const _captured_0 = $$Pieces_side_at(_ps_0, _to_0, _enemy_0);
  const _ps2_0 = $$Pieces_move($$Pieces_capture(_ps_0, _to_0, _enemy_0), _from_0, _to_0);
  const _b2_0 = $$hand_after($$Side_is_blue(_turn_0), _b_0, _card_0, _table_0);
  const _r2_0 = $$hand_after($$Bool_not($$Side_is_blue(_turn_0)), _r_0, _card_0, _table_0);
  const _q2_0 = $$quiet_after(_captured_0, _q_0);
  const _key_0 = $$Game_key(_ps2_0, _b2_0, _r2_0, _card_0, _enemy_0);
  const _h2_0 = $$history_after(_captured_0, _key_0, _h_0);
  const _draw_0 = $$Game_drawn(_h2_0, _q2_0);
  return {$: "Game", "turn": _enemy_0, "pieces": _ps2_0, "blue": _b2_0, "red": _r2_0, "table": _card_0, "quiet": _q2_0, "history": _h2_0, "result": $$outcome_after(_win_0, _turn_0, _draw_0)};
}

function $apply(_g_0, _m_0) {
  const _turn_0 = _g_0["turn"];
  const _ps_0 = _g_0["pieces"];
  const _b_0 = _g_0["blue"];
  const _r_0 = _g_0["red"];
  const _table_0 = _g_0["table"];
  const _q_0 = _g_0["quiet"];
  const _h_0 = _g_0["history"];
  const _card_0 = _m_0["card"];
  const _from_0 = _m_0["from"];
  const _to_0 = _m_0["to"];
  return $apply_go($$won(_ps_0, $$Side_other(_turn_0), _to_0), _turn_0, _ps_0, _b_0, _r_0, _table_0, _q_0, _h_0, _card_0, _from_0, _to_0);
}

function $play_go(_legal_0, _g_0, _m_0) {
  if (_legal_0) {
    return $apply(_g_0, _m_0);
  } else {
    return _g_0;
  }
}

function $play(_g_0, _m_0) {
  return $play_go($$is_legal(_g_0, _m_0), _g_0, _m_0);
}

function $replay($0, $1) {
  for (;;) {
    {
      const _moves_0 = $0;
      const _g_0 = $1;
      if (_moves_0.$ === "Nil") {
        return _g_0;
      } else {
        const _m_0 = _moves_0["head"];
        const _rest_0 = _moves_0["tail"];
        $0 = _rest_0;
        $1 = $$play(_g_0, _m_0);
        continue;
      }
    }
  }
}

function $after(_setup_0, _moves_0) {
  return $replay(_moves_0, $$start(_setup_0));
}

function $turn_of(_g_0) {
  return $Game_turn(_g_0);
}

function $outcome(_g_0) {
  return $Game_result(_g_0);
}

function $is_over(_g_0) {
  return $Outcome_is_over($$Game_result(_g_0));
}

function $has_winner(_g_0) {
  return $Outcome_is_win($$outcome(_g_0));
}

function $repetitions(_setup_0, _moves_0) {
  const _h_0 = $$Game_history($$after(_setup_0, _moves_0));
  return $U32s_count(_h_0, $$U32s_nth(_h_0, 0));
}

function $quiet_turns(_setup_0, _moves_0) {
  return $Game_quiet($$after(_setup_0, _moves_0));
}

function $has_legal_move(_g_0) {
  return $Actions_nonempty($$legal_moves(_g_0));
}

function $card_count(_g_0) {
  const _x_0 = $$U32s_len($$Game_hand(_g_0, {$: "Blue"}));
  const _x_1 = $$U32s_len($$Game_hand(_g_0, {$: "Red"}));
  const _x_2 = nat_chk(_x_0 + _x_1);
  return nat_chk(_x_2 + 1);
}

function $piece_count(_g_0) {
  return $Pieces_len($$Game_pieces(_g_0));
}

function $enemy_home(_g_0) {
  return $Side_home($$Side_other($$Game_turn(_g_0)));
}

function $enemy_teacher_square(_g_0) {
  return $Pieces_teacher_of($$Game_pieces(_g_0), $$Side_other($$Game_turn(_g_0)));
}

function $enemy_at(_g_0, _square_0) {
  return $Pieces_side_at($$Game_pieces(_g_0), _square_0, $$Side_other($$Game_turn(_g_0)));
}

function $own_at(_g_0, _square_0) {
  return $Pieces_side_at($$Game_pieces(_g_0), _square_0, $$Game_turn(_g_0));
}

function $own_cards(_g_0, _s_0) {
  return $Game_hand(_g_0, _s_0);
}

function $table_card(_g_0) {
  return $Game_table(_g_0);
}

function $with_enemy_hand(_g_0, _s_0, _cards_0) {
  const _t_0 = _g_0["turn"];
  const _p_0 = _g_0["pieces"];
  const _b_0 = _g_0["blue"];
  const __0 = _g_0["red"];
  const _tb_0 = _g_0["table"];
  const _q_0 = _g_0["quiet"];
  const _h_0 = _g_0["history"];
  const _res_0 = _g_0["result"];
  if (_s_0.$ === "Blue") {
    return {$: "Game", "turn": _t_0, "pieces": _p_0, "blue": _b_0, "red": _cards_0, "table": _tb_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  } else {
    return {$: "Game", "turn": _t_0, "pieces": _p_0, "blue": _cards_0, "red": __0, "table": _tb_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  }
}

function $reveal_hand_go(_known_0, _h_0, _card_0) {
  if (_known_0) {
    return _h_0;
  } else {
    return $U32s_replace(_h_0, 99, _card_0);
  }
}

function $reveal_hand(_h_0, _card_0) {
  return $reveal_hand_go($$U32s_has(_h_0, _card_0), _h_0, _card_0);
}

function $play_revealed(_g_0, _m_0) {
  const _c_0 = _m_0["card"];
  const __0 = _m_0["from"];
  const __1 = _m_0["to"];
  return $play($$with_enemy_hand(_g_0, $$Side_other($$Game_turn(_g_0)), $$reveal_hand($$Game_hand(_g_0, $$Game_turn(_g_0)), _c_0)), {$: "Action", "card": _c_0, "from": __0, "to": __1});
}

function $View_make(_s_0, _b_0, _r_0, _tb_0, _t_0, _p_0, _q_0, _h_0, _res_0) {
  if (_s_0.$ === "Blue") {
    return {$: "View", "side": {$: "Blue"}, "own": _b_0, "table": _tb_0, "turn": _t_0, "pieces": _p_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  } else {
    return {$: "View", "side": {$: "Red"}, "own": _r_0, "table": _tb_0, "turn": _t_0, "pieces": _p_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  }
}

function $view(_g_0, _s_0) {
  const _t_0 = _g_0["turn"];
  const _p_0 = _g_0["pieces"];
  const _b_0 = _g_0["blue"];
  const _r_0 = _g_0["red"];
  const _tb_0 = _g_0["table"];
  const _q_0 = _g_0["quiet"];
  const _h_0 = _g_0["history"];
  const _res_0 = _g_0["result"];
  return $View_make(_s_0, _b_0, _r_0, _tb_0, _t_0, _p_0, _q_0, _h_0, _res_0);
}

function $View_own(_v_0) {
  const _o_0 = _v_0["own"];
  return _o_0;
}

function $View_table(_v_0) {
  const _t_0 = _v_0["table"];
  return _t_0;
}

function $View_side(_v_0) {
  const _s_0 = _v_0["side"];
  return _s_0;
}

function $View_result(_v_0) {
  const _r_0 = _v_0["result"];
  return _r_0;
}

function $View_key(_v_0) {
  const _h_0 = _v_0["history"];
  return $U32s_nth(_h_0, 0);
}

function $View_guess_go(_s_0, _o_0, _e_0, _tb_0, _t_0, _p_0, _q_0, _h_0, _res_0) {
  if (_s_0.$ === "Blue") {
    return {$: "Game", "turn": _t_0, "pieces": _p_0, "blue": _o_0, "red": _e_0, "table": _tb_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  } else {
    return {$: "Game", "turn": _t_0, "pieces": _p_0, "blue": _e_0, "red": _o_0, "table": _tb_0, "quiet": _q_0, "history": _h_0, "result": _res_0};
  }
}

function $View_guess(_v_0, _enemy_0) {
  const _s_0 = _v_0["side"];
  const _o_0 = _v_0["own"];
  const _tb_0 = _v_0["table"];
  const _t_0 = _v_0["turn"];
  const _p_0 = _v_0["pieces"];
  const _q_0 = _v_0["quiet"];
  const _h_0 = _v_0["history"];
  const _res_0 = _v_0["result"];
  return $View_guess_go(_s_0, _o_0, _enemy_0, _tb_0, _t_0, _p_0, _q_0, _h_0, _res_0);
}

function $View_sample_enemy(_v_0, _r_0) {
  return $draw_n(2, $$U32s_remove($$U32s_remove($$U32s_remove($$U32s_range(18), $$View_table(_v_0)), $$U32s_nth($$View_own(_v_0), 0)), $$U32s_nth($$View_own(_v_0), 1)), _r_0);
}

function $find_win_pick(_hit_0, _a_0, _b_0) {
  if (_hit_0) {
    return {$: "Some", "value": _a_0};
  } else {
    return _b_0;
  }
}

function $find_win(_ms_0, _home_0, _tsq_0) {
  if (_ms_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _m_0 = _ms_0["head"];
    const _rest_0 = _ms_0["tail"];
    const _x_0 = $$Cell_eq($$to_of(_m_0), _home_0);
    const _x_1 = $$Cell_is(_tsq_0, $$to_of(_m_0));
    return $find_win_pick((_x_0 || _x_1), _m_0, $$find_win(_rest_0, _home_0, _tsq_0));
  }
}

function $quick_move_pick(_w_0, _ms_0, _r_0) {
  if (_w_0.$ === "None") {
    const _x_0 = $$Actions_len(_ms_0);
    const _x_1 = (_x_0 >>>0);
    const _x_2 = (_x_1 === 0 ? _r_0 : _r_0 % _x_1);
    return $Actions_nth(_ms_0, (_x_2 ));
  } else {
    const _a_0 = _w_0["value"];
    return _a_0;
  }
}

function $quick_move(_g_0, _r_0) {
  const _ms_0 = $$legal_moves(_g_0);
  return $quick_move_pick($$find_win(_ms_0, $$enemy_home(_g_0), $$enemy_teacher_square(_g_0)), _ms_0, _r_0);
}

function $playout($0, $1, $2, $3) {
  for (;;) {
    {
      const _fuel_0 = $0;
      const _over_0 = $1;
      const _g_0 = $2;
      const _r_0 = $3;
      if (_fuel_0 == 0) {
        if (_over_0) {
          return $Game_result(_g_0);
        } else {
          return {$: "Draw"};
        }
      } else {
        const _f_0 = (_fuel_0 - 1);
        if (_over_0) {
          return $Game_result(_g_0);
        } else {
          const _g2_0 = $$play(_g_0, $$quick_move(_g_0, _r_0));
          $0 = _f_0;
          $1 = $$is_over(_g2_0);
          $2 = _g2_0;
          $3 = $$rng(_r_0);
          continue;
        }
      }
    }
  }
}

function $Chances_add(_c_0, _o_0) {
  const _b_0 = _c_0["blue"];
  const _r_0 = _c_0["red"];
  const _d_0 = _c_0["draws"];
  const _n_0 = _c_0["games"];
  if (_o_0.$ === "Winner") {
    const _t_0 = _o_0["side"];
    if (_t_0.$ === "Blue") {
      return {$: "Chances", "blue": nat_chk(_b_0 + 1), "red": _r_0, "draws": _d_0, "games": nat_chk(_n_0 + 1)};
    } else {
      return {$: "Chances", "blue": _b_0, "red": nat_chk(_r_0 + 1), "draws": _d_0, "games": nat_chk(_n_0 + 1)};
    }
  } else {
    return {$: "Chances", "blue": _b_0, "red": _r_0, "draws": nat_chk(_d_0 + 1), "games": nat_chk(_n_0 + 1)};
  }
}

function $chances_run($0, $1, $2, $3) {
  for (;;) {
    {
      const _n_0 = $0;
      const _v_0 = $1;
      const _r_0 = $2;
      const _acc_0 = $3;
      if (_n_0 == 0) {
        return _acc_0;
      } else {
        const _p_0 = (_n_0 - 1);
        const _g_0 = $$View_guess(_v_0, $$View_sample_enemy(_v_0, _r_0));
        $0 = _p_0;
        $1 = _v_0;
        $2 = $$rng($$rng(_r_0));
        $3 = $$Chances_add(_acc_0, $$playout(240, $$is_over(_g_0), _g_0, $$rng(_r_0)));
        continue;
      }
    }
  }
}

function $chances_all(_o_0, _n_0) {
  if (_o_0.$ === "Winner") {
    const _t_0 = _o_0["side"];
    if (_t_0.$ === "Blue") {
      return {$: "Chances", "blue": _n_0, "red": 0, "draws": 0, "games": _n_0};
    } else {
      return {$: "Chances", "blue": 0, "red": _n_0, "draws": 0, "games": _n_0};
    }
  } else {
    return {$: "Chances", "blue": 0, "red": 0, "draws": _n_0, "games": _n_0};
  }
}

function $chances_go(_over_0, _v_0, _n_0) {
  if (_over_0) {
    return $chances_all($$View_result(_v_0), _n_0);
  } else {
    const _x_0 = $$mix($$View_key(_v_0));
    return $chances_run(_n_0, _v_0, ((_x_0 + 1) >>> 0), {$: "Chances", "blue": 0, "red": 0, "draws": 0, "games": 0});
  }
}

function $chances_n(_v_0, _n_0) {
  return $chances_go($$Outcome_is_over($$View_result(_v_0)), _v_0, _n_0);
}

function $chances(_v_0) {
  return $chances_n(_v_0, 100);
}

function $Chances_wins_of(_c_0, _s_0) {
  const _b_0 = _c_0["blue"];
  const __0 = _c_0["red"];
  if (_s_0.$ === "Blue") {
    return _b_0;
  } else {
    return __0;
  }
}

function $Chances_draws(_c_0) {
  const _d_0 = _c_0["draws"];
  return _d_0;
}

function $Chances_total(_c_0) {
  const _b_0 = _c_0["blue"];
  const _r_0 = _c_0["red"];
  const _d_0 = _c_0["draws"];
  const _x_0 = nat_chk(_b_0 + _r_0);
  return nat_chk(_x_0 + _d_0);
}

function $Chances_games(_c_0) {
  const _n_0 = _c_0["games"];
  return _n_0;
}

function $bot_points(_o_0, _me_0) {
  if (_o_0.$ === "Winner") {
    const _s_0 = _o_0["side"];
    return $sel($$Side_same(_s_0, _me_0), 2, 0);
  } else {
    return 1;
  }
}

function $bot_score($0, $1, $2, $3, $4, $5) {
  for (;;) {
    {
      const _n_0 = $0;
      const _v_0 = $1;
      const _m_0 = $2;
      const _me_0 = $3;
      const _r_0 = $4;
      const _acc_0 = $5;
      if (_n_0 == 0) {
        return _acc_0;
      } else {
        const _p_0 = (_n_0 - 1);
        const _g_0 = $$play($$View_guess(_v_0, $$View_sample_enemy(_v_0, _r_0)), _m_0);
        const _o_0 = $$playout(240, $$is_over(_g_0), _g_0, $$rng(_r_0));
        const _x_0 = $$bot_points(_o_0, _me_0);
        $0 = _p_0;
        $1 = _v_0;
        $2 = _m_0;
        $3 = _me_0;
        $4 = $$rng($$rng(_r_0));
        $5 = ((_acc_0 + _x_0) >>> 0);
        continue;
      }
    }
  }
}

function $bot_keep(_better_0, _m_0, _best_0) {
  if (_better_0) {
    return _m_0;
  } else {
    return _best_0;
  }
}

function $bot_best($0, $1, $2, $3, $4, $5) {
  for (;;) {
    {
      const _ms_0 = $0;
      const _n_0 = $1;
      const _v_0 = $2;
      const _r_0 = $3;
      const _best_0 = $4;
      const _best_score_0 = $5;
      if (_ms_0.$ === "Nil") {
        return _best_0;
      } else {
        const _m_0 = _ms_0["head"];
        const _rest_0 = _ms_0["tail"];
        const _s_0 = $$bot_score(_n_0, _v_0, _m_0, $$View_side(_v_0), _r_0, 0);
        const _better_0 = (_best_score_0 < _s_0);
        $0 = _rest_0;
        $1 = _n_0;
        $2 = _v_0;
        $3 = $$rng(_r_0);
        $4 = $$bot_keep(_better_0, _m_0, _best_0);
        $5 = $$sel(_better_0, _s_0, _best_score_0);
        continue;
      }
    }
  }
}

function $bot_by_level(_lvl_0, _ms_0, _v_0, _r_0) {
  if (_lvl_0 == 0) {
    const _x_0 = $$Actions_len(_ms_0);
    const _x_1 = (_x_0 >>>0);
    const _x_2 = (_x_1 === 0 ? _r_0 : _r_0 % _x_1);
    return $Actions_nth(_ms_0, (_x_2 ));
  } else if (_lvl_0 == 1) {
    return $bot_best(_ms_0, 24, _v_0, _r_0, $$Actions_nth(_ms_0, 0), 0);
  } else {
    return $bot_best(_ms_0, 160, _v_0, _r_0, $$Actions_nth(_ms_0, 0), 0);
  }
}

function $bot_decide_go(_w_0, _ms_0, _v_0, _lvl_0, _r_0) {
  if (_w_0.$ === "None") {
    return $bot_by_level(_lvl_0, _ms_0, _v_0, _r_0);
  } else {
    const _a_0 = _w_0["value"];
    return _a_0;
  }
}

function $bot_decide(_v_0, _lvl_0, _r_0) {
  const _g_0 = $$View_guess(_v_0, {$: "Con", "head": 99, "tail": {$: "Con", "head": 99, "tail": {$: "Nil"}}});
  const _ms_0 = $$legal_moves(_g_0);
  return $bot_decide_go($$find_win(_ms_0, $$enemy_home(_g_0), $$enemy_teacher_square(_g_0)), _ms_0, _v_0, _lvl_0, _r_0);
}

function $Bit_char(_b_0) {
  if (_b_0) {
    return "1";
  } else {
    return "0";
  }
}

function $Bits_show(_n_0, _w_0, _rest_0) {
  if (_n_0 == 0) {
    return _rest_0;
  } else {
    const _p_0 = (_n_0 - 1);
    const _b_0 = _w_0["head"];
    const _t_0 = _w_0["tail"];
    return ($$Bit_char(_b_0) + $$Bits_show(_p_0, _t_0, _rest_0));
  }
}

function $Bits_bit_go(_one_0, _zero_0) {
  if (_one_0) {
    return {$: "Some", "value": true};
  } else {
    if (_zero_0) {
      return {$: "Some", "value": false};
    } else {
      return {$: "None"};
    }
  }
}

function $Bits_bit(_c_0) {
  return $Bits_bit_go($$Char_is_eq(_c_0, "1"), $$Char_is_eq(_c_0, "0"));
}

function $Bits_cons(_b_0, _w_0) {
  if (_b_0.$ === "Some") {
    const _x_0 = _b_0["value"];
    if (_w_0.$ === "Some") {
      const _y_0 = _w_0["value"];
      return {$: "Some", "value": {$: "WCon", "head": _x_0, "tail": _y_0}};
    } else {
      return {$: "None"};
    }
  } else {
    return {$: "None"};
  }
}

function $Bits_read(_n_0, _s_0) {
  if (_n_0 == 0) {
    return {$: "Some", "value": {$: "WNil"}};
  } else {
    const _p_0 = (_n_0 - 1);
    if (_s_0 === "") {
      return {$: "None"};
    } else {
      const _c_0 = _s_0.slice(0, char_len(_s_0));
      const _t_0 = _s_0.slice(char_len(_s_0));
      return $Bits_cons($$Bits_bit(_c_0), $$Bits_read(_p_0, _t_0));
    }
  }
}

function $Bits_drop($0, $1) {
  for (;;) {
    {
      const _n_0 = $0;
      const _s_0 = $1;
      if (_n_0 == 0) {
        return _s_0;
      } else {
        const _p_0 = (_n_0 - 1);
        if (_s_0 === "") {
          return "";
        } else {
          const _t_0 = _s_0.slice(char_len(_s_0));
          $0 = _p_0;
          $1 = _t_0;
          continue;
        }
      }
    }
  }
}

function $U32_bits(_x_0, _rest_0) {
  const _w_0 = u32_to_word(_x_0);
  return $Bits_show(32, _w_0, _rest_0);
}

function $U32_of_word(_m_0) {
  if (_m_0.$ === "Some") {
    const _w_0 = _m_0["value"];
    return {$: "Some", "value": word_to_u32(_w_0)};
  } else {
    return {$: "None"};
  }
}

function $U32_of_bits(_s_0) {
  return $U32_of_word($$Bits_read(32, _s_0));
}

function $Invite_encode(_i_0) {
  const _r_0 = _i_0["room"];
  return $U32_bits(_r_0, "");
}

function $Invite_of(_m_0) {
  if (_m_0.$ === "Some") {
    const _n_0 = _m_0["value"];
    return {$: "Some", "value": {$: "Invite", "room": _n_0}};
  } else {
    return {$: "None"};
  }
}

function $Invite_decode(_s_0) {
  return $Invite_of($$U32_of_bits(_s_0));
}

function $Message_encode(_m_0) {
  if (_m_0.$ === "Played") {
    const _t_0 = _m_0["move"];
    const _c_0 = _t_0["card"];
    const _f_0 = _t_0["from"];
    const _t_1 = _t_0["to"];
    return ("P" + $$U32_bits(_c_0, $$U32_bits($$Cell_u32(_f_0), $$U32_bits($$Cell_u32(_t_1), ""))));
  } else {
    return "R";
  }
}

function $Message_played(_a_0, _b_0, _c_0) {
  if (_a_0.$ === "Some") {
    const _x_0 = _a_0["value"];
    if (_b_0.$ === "Some") {
      const _y_0 = _b_0["value"];
      if (_c_0.$ === "Some") {
        const _z_0 = _c_0["value"];
        return {$: "Some", "value": {$: "Played", "move": {$: "Action", "card": _x_0, "from": _y_0, "to": _z_0}}};
      } else {
        return {$: "None"};
      }
    } else {
      return {$: "None"};
    }
  } else {
    return {$: "None"};
  }
}

function $Cell_of_maybe(_m_0) {
  if (_m_0.$ === "Some") {
    const _x_0 = _m_0["value"];
    return $Cell_of_u32(_x_0);
  } else {
    return {$: "None"};
  }
}

function $Message_parse(_body_0) {
  const _rest_0 = $$Bits_drop(32, _body_0);
  return $Message_played($$U32_of_bits(_body_0), $$Cell_of_maybe($$U32_of_bits(_rest_0)), $$Cell_of_maybe($$U32_of_bits($$Bits_drop(32, _rest_0))));
}

function $Message_decode_resign(_t_0) {
  if (_t_0 === "") {
    return {$: "Some", "value": {$: "Resign"}};
  } else {
    return {$: "None"};
  }
}

function $Message_decode_go(_p_0, _r_0, _t_0) {
  if (_p_0) {
    return $Message_parse(_t_0);
  } else {
    if (_r_0) {
      return $Message_decode_resign(_t_0);
    } else {
      return {$: "None"};
    }
  }
}

function $Message_decode(_s_0) {
  if (_s_0 === "") {
    return {$: "None"};
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    return $Message_decode_go($$Char_is_eq(_h_0, "P"), $$Char_is_eq(_h_0, "R"), _t_0);
  }
}

function $Message_code(_m_0) {
  if (_m_0.$ === "Some") {
    const _t_0 = _m_0["value"];
    if (_t_0.$ === "Played") {
      const _a_0 = _t_0["move"];
      const _x_0 = $$Action_code(_a_0);
      return ((_x_0 + 1) >>> 0);
    } else {
      return 4294967295;
    }
  } else {
    return 0;
  }
}

function $ending_win(_gone_0) {
  if (_gone_0) {
    return {$: "KeeperTaken"};
  } else {
    return {$: "ReachedGoal"};
  }
}

function $ending_draw(_stalled_0) {
  if (_stalled_0) {
    return {$: "Stalled"};
  } else {
    return {$: "Repeated"};
  }
}

function $ending_of(_o_0, _g_0) {
  if (_o_0.$ === "Ongoing") {
    return {$: "Playing"};
  } else if (_o_0.$ === "Winner") {
    const _s_0 = _o_0["side"];
    return $ending_win($$Cell_none($$Pieces_teacher_of($$Game_pieces(_g_0), $$Side_other(_s_0))));
  } else {
    return $ending_draw($$Nat_is_ge($$Game_quiet(_g_0), 20));
  }
}

function $ending(_g_0) {
  return $ending_of($$Game_result(_g_0), _g_0);
}

function $Ending_is_over(_e_0) {
  if (_e_0.$ === "Playing") {
    return false;
  } else {
    return true;
  }
}

function $Click_play(_m_0) {
  const _c_0 = _m_0["card"];
  const _f_0 = _m_0["from"];
  const _t_0 = _m_0["to"];
  return {$: "Play", "card": _c_0, "from": $$Cell_u32(_f_0), "to": $$Cell_u32(_t_0)};
}

function $Action_of_parts(_card_0, _from_0, _to_0) {
  return {$: "Action", "card": _card_0, "from": $$Cell_or_corner($$Cell_of_u32(_from_0)), "to": $$Cell_or_corner($$Cell_of_u32(_to_0))};
}

function $Actions_keep(_c_0, _m_0, _rest_0) {
  if (_c_0) {
    return {$: "Con", "head": _m_0, "tail": _rest_0};
  } else {
    return _rest_0;
  }
}

function $Actions_with_card(_xs_0, _card_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _m_0 = _xs_0["head"];
    const _rest_0 = _xs_0["tail"];
    const _x_0 = $$Action_card(_m_0);
    return $Actions_keep((_x_0 === _card_0), _m_0, $$Actions_with_card(_rest_0, _card_0));
  }
}

function $Actions_with_to(_xs_0, _to_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _m_0 = _xs_0["head"];
    const _rest_0 = _xs_0["tail"];
    return $Actions_keep($$Cell_eq($$to_of(_m_0), _to_0), _m_0, $$Actions_with_to(_rest_0, _to_0));
  }
}

function $Actions_with_from(_xs_0, _from_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _m_0 = _xs_0["head"];
    const _rest_0 = _xs_0["tail"];
    return $Actions_keep($$Cell_is(_from_0, $$Action_from(_m_0)), _m_0, $$Actions_with_from(_rest_0, _from_0));
  }
}

function $click_moves(_mine_0, _g_0) {
  if (_mine_0) {
    return $legal_moves(_g_0);
  } else {
    return {$: "Nil"};
  }
}

function $click_select(_mine_0, _same_0, _sq_0) {
  if (_mine_0) {
    if (!_same_0) {
      return {$: "Select", "sq": $$Cell_u32(_sq_0)};
    } else {
      return {$: "Clear"};
    }
  } else {
    return {$: "Clear"};
  }
}

function $click_crowd(_mine_0, _sq_0) {
  if (_mine_0) {
    return {$: "Select", "sq": $$Cell_u32(_sq_0)};
  } else {
    return {$: "Crowded"};
  }
}

function $click_one(_rest_0, _m_0, _mine_0, _sq_0) {
  if (_rest_0.$ === "Nil") {
    return $Click_play(_m_0);
  } else {
    return $click_crowd(_mine_0, _sq_0);
  }
}

function $click_reach(_reach_0, _mine_0, _sq_0) {
  if (_reach_0.$ === "Nil") {
    return $click_select(_mine_0, false, _sq_0);
  } else {
    const _m_0 = _reach_0["head"];
    const _rest_0 = _reach_0["tail"];
    return $click_one(_rest_0, _m_0, _mine_0, _sq_0);
  }
}

function $click_free(_none_0, _reach_0, _mine_0, _same_0, _sq_0) {
  if (_none_0) {
    return $click_reach(_reach_0, _mine_0, _sq_0);
  } else {
    return $click_select(_mine_0, _same_0, _sq_0);
  }
}

function $click_go(_hit_0, _none_0, _reach_0, _mine_0, _same_0, _sq_0) {
  if (_hit_0.$ === "Con") {
    const _m_0 = _hit_0["head"];
    return $Click_play(_m_0);
  } else {
    return $click_free(_none_0, _reach_0, _mine_0, _same_0, _sq_0);
  }
}

function $click(_g_0, _me_0, _card_0, _s_0, _sq_0) {
  const _moves_0 = $$Actions_with_card($$click_moves($$Side_same($$Game_turn(_g_0), _me_0), _g_0), _card_0);
  const _reach_0 = $$Actions_with_to(_moves_0, _sq_0);
  const _hit_0 = $$Actions_with_from(_reach_0, _s_0);
  return $click_go(_hit_0, $$Cell_none(_s_0), _reach_0, $$Pieces_side_at($$Game_pieces(_g_0), _sq_0, _me_0), $$Cell_is(_s_0, _sq_0), _sq_0);
}

function $click_api(_at_0, _g_0, _me_0, _card_0, _s_0) {
  if (_at_0.$ === "None") {
    return {$: "Clear"};
  } else {
    const _sq_0 = _at_0["value"];
    return $click(_g_0, _me_0, _card_0, $$Cell_of_u32(_s_0), _sq_0);
  }
}

function $click_ok_of(_c_0, _g_0, _me_0) {
  if (_c_0.$ === "Play") {
    const _card_0 = _c_0["card"];
    const _f_0 = _c_0["from"];
    const _t_0 = _c_0["to"];
    return $Bool_and($$Side_same($$Game_turn(_g_0), _me_0), $$is_legal(_g_0, $$Action_of_parts(_card_0, _f_0, _t_0)));
  } else {
    return true;
  }
}

function $click_ok(_g_0, _me_0, _card_0, _s_0, _sq_0) {
  return $click_ok_of($$click_api($$Cell_of_u32(_sq_0), _g_0, _me_0, _card_0, _s_0), _g_0, _me_0);
}

function $scene_of(_ps_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ps_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["teacher"];
    const _q_0 = _t_0["square"];
    const _rest_0 = _ps_0["tail"];
    return {$: "Con", "head": {$: "Token", "side": _s_0, "keeper": _t_1, "cell": _q_0}, "tail": $$scene_of(_rest_0)};
  }
}

function $scene(_g_0) {
  return $scene_of($$Game_pieces(_g_0));
}

function $Tokens_code_at(_ts_0, _sq_0) {
  if (_ts_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ts_0["head"];
    const _s_0 = _t_0["side"];
    const _t_1 = _t_0["keeper"];
    const _q_0 = _t_0["cell"];
    const _rest_0 = _ts_0["tail"];
    return $sel($$Cell_eq(_q_0, _sq_0), $$Piece_code(_s_0, _t_1), $$Tokens_code_at(_rest_0, _sq_0));
  }
}

function $Tokens_len(_ts_0) {
  if (_ts_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ts_0["tail"];
    return nat_chk($$Tokens_len(_t_0) + 1);
  }
}

function $Tokens_count_add(_hit_0, _n_0) {
  if (_hit_0) {
    return nat_chk(_n_0 + 1);
  } else {
    return _n_0;
  }
}

function $Tokens_count(_ts_0, _side_0) {
  if (_ts_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ts_0["head"];
    const _s_0 = _t_0["side"];
    const _rest_0 = _ts_0["tail"];
    return $Tokens_count_add($$Side_same(_s_0, _side_0), $$Tokens_count(_rest_0, _side_0));
  }
}

function $Tokens_cells(_ts_0) {
  if (_ts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ts_0["head"];
    const _q_0 = _t_0["cell"];
    const _rest_0 = _ts_0["tail"];
    return {$: "Con", "head": _q_0, "tail": $$Tokens_cells(_rest_0)};
  }
}

function $Cells_unstacked(_cs_0) {
  if (_cs_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _cs_0["head"];
    const _t_0 = _cs_0["tail"];
    return $Bool_and($$Bool_not($$Cells_has(_t_0, _h_0)), $$Cells_unstacked(_t_0));
  }
}

function $Tokens_nth($0, $1) {
  for (;;) {
    {
      const _ts_0 = $0;
      const _n_0 = $1;
      if (_ts_0.$ === "Nil") {
        return {$: "Token", "side": {$: "Blue"}, "keeper": false, "cell": {$: "Cell", "col": {$: "F0"}, "row": {$: "F0"}}};
      } else {
        const _h_0 = _ts_0["head"];
        const __0 = _ts_0["tail"];
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

function $Token_pack(_t_0) {
  const _s_0 = _t_0["side"];
  const _k_0 = _t_0["keeper"];
  const _q_0 = _t_0["cell"];
  const _x_0 = $$Piece_code(_s_0, _k_0);
  const _x_1 = (Math.imul(_x_0, 64) >>> 0);
  const _x_2 = $$Cell_u32(_q_0);
  return ((_x_1 + _x_2) >>> 0);
}

function $Nats_has(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_1 = $$Nat_is_eq(_h_0, _x_0);
    const _x_2 = $$Nats_has(_t_0, _x_0);
    return (_x_1 || _x_2);
  }
}

function $Nats_keep(_drop_0, _h_0, _rest_0) {
  if (_drop_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $Nats_without(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Nats_keep($$Nat_is_eq(_h_0, _x_0), _h_0, $$Nats_without(_t_0, _x_0));
  }
}

function $Nats_nth($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      if (_xs_0.$ === "Nil") {
        return 99;
      } else {
        const _h_0 = _xs_0["head"];
        const __0 = _xs_0["tail"];
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

function $Proto_mine(_host_0) {
  if (_host_0) {
    return {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Nil"}}};
  } else {
    return {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Nil"}}};
  }
}

function $Proto_handed(_host_0) {
  if (_host_0) {
    return {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Con", "head": 4, "tail": {$: "Nil"}}}};
  } else {
    return {$: "Con", "head": 0, "tail": {$: "Con", "head": 1, "tail": {$: "Con", "head": 4, "tail": {$: "Nil"}}}};
  }
}

function $Proto_plan(_host_0) {
  if (_host_0) {
    return {$: "Con", "head": 1, "tail": {$: "Con", "head": 2, "tail": {$: "Con", "head": 4, "tail": {$: "Con", "head": 6, "tail": {$: "Con", "head": 7, "tail": {$: "Nil"}}}}}};
  } else {
    return {$: "Con", "head": 1, "tail": {$: "Con", "head": 2, "tail": {$: "Con", "head": 3, "tail": {$: "Con", "head": 5, "tail": {$: "Con", "head": 7, "tail": {$: "Nil"}}}}}};
  }
}

function $Proto_expected(_host_0, _i_0) {
  return $U32s_nth($$Proto_plan(_host_0), _i_0);
}

function $Proto_index_pick(_hit_0, _rest_0) {
  if (_hit_0) {
    return 0;
  } else {
    return nat_chk(_rest_0 + 1);
  }
}

function $Proto_index(_xs_0, _k_0) {
  if (_xs_0.$ === "Nil") {
    return 99;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Proto_index_pick((_h_0 === _k_0), $$Proto_index(_t_0, _k_0));
  }
}

function $Order_is_cheat(_o_0) {
  if (_o_0.$ === "Cheat") {
    return true;
  } else {
    return false;
  }
}

function $Proto_order_of(_c_0) {
  if (_c_0.$ === "EQ") {
    return {$: "Take"};
  } else if (_c_0.$ === "GT") {
    return {$: "Hold"};
  } else {
    return {$: "Cheat"};
  }
}

function $Proto_order_planned(_known_0, _j_0, _i_0) {
  if (_known_0) {
    return $Proto_order_of(cmp_new(_j_0, _i_0));
  } else {
    return {$: "Cheat"};
  }
}

function $Proto_order_setup(_j_0, _i_0) {
  return $Proto_order_planned((_j_0 < 5), _j_0, _i_0);
}

function $Proto_order_move(_playing_0) {
  if (_playing_0) {
    return {$: "Take"};
  } else {
    return {$: "Cheat"};
  }
}

function $Proto_order_go(_move_0, _resign_0, _host_0, _i_0, _k_0) {
  if (_move_0) {
    return $Proto_order_move($$Nat_is_ge(_i_0, 5));
  } else {
    if (_resign_0) {
      return {$: "Take"};
    } else {
      return $Proto_order_setup($$Proto_index($$Proto_plan(_host_0), _k_0), _i_0);
    }
  }
}

function $Proto_order(_host_0, _i_0, _k_0) {
  return $Proto_order_go((_k_0 === 8), (_k_0 === 9), _host_0, _i_0, _k_0);
}

function $Proto_coin_ok(_matches_0, _bit_0) {
  const _x_0 = (_bit_0 === 0);
  const _x_1 = (_bit_0 === 1);
  return $Bool_and(_matches_0, (_x_0 || _x_1));
}

function $Opp_start(_host_0, _table_0) {
  return {$: "Opp", "hidden": $$Proto_mine($$Bool_not(_host_0)), "seen": {$: "Nil"}, "table": _table_0};
}

function $Opp_hidden(_o_0) {
  const _h_0 = _o_0["hidden"];
  return _h_0;
}

function $Opp_seen(_o_0) {
  const _s_0 = _o_0["seen"];
  return _s_0;
}

function $Opp_table(_o_0) {
  const _t_0 = _o_0["table"];
  return _t_0;
}

function $Opp_check(_ok_0, _pos_0, _hid_0, _seen_0, _tb_0, _c_0) {
  if (_ok_0) {
    return {$: "Accepted", "opp": {$: "Opp", "hidden": $$Nats_without(_hid_0, _pos_0), "seen": {$: "Con", "head": _tb_0, "tail": _seen_0}, "table": _c_0}};
  } else {
    return {$: "Rejected", "reason": 2};
  }
}

function $Opp_proof(_p_0, _hid_0, _seen_0, _tb_0, _c_0) {
  if (_p_0.$ === "NoProof") {
    return {$: "Rejected", "reason": 1};
  } else {
    const _pos_0 = _p_0["pos"];
    const _opened_0 = _p_0["card"];
    return $Opp_check($$Bool_and($$Nats_has(_hid_0, _pos_0), (_opened_0 === _c_0)), _pos_0, _hid_0, _seen_0, _tb_0, _c_0);
  }
}

function $Opp_play_go(_known_0, _hid_0, _seen_0, _tb_0, _c_0, _p_0) {
  if (_known_0) {
    return {$: "Accepted", "opp": {$: "Opp", "hidden": _hid_0, "seen": {$: "Con", "head": _tb_0, "tail": $$U32s_remove(_seen_0, _c_0)}, "table": _c_0}};
  } else {
    return $Opp_proof(_p_0, _hid_0, _seen_0, _tb_0, _c_0);
  }
}

function $Opp_play(_o_0, _c_0, _p_0) {
  const _hid_0 = _o_0["hidden"];
  const _seen_0 = _o_0["seen"];
  const _tb_0 = _o_0["table"];
  return $Opp_play_go($$U32s_has(_seen_0, _c_0), _hid_0, _seen_0, _tb_0, _c_0, _p_0);
}

function $Opp_i_played(_o_0, _c_0) {
  const _hid_0 = _o_0["hidden"];
  const _seen_0 = _o_0["seen"];
  return {$: "Opp", "hidden": _hid_0, "seen": _seen_0, "table": _c_0};
}

function $Verdict_ok(_v_0) {
  if (_v_0.$ === "Accepted") {
    return true;
  } else {
    return false;
  }
}

function $Verdict_opp(_v_0, _d_0) {
  if (_v_0.$ === "Accepted") {
    const _o_0 = _v_0["opp"];
    return _o_0;
  } else {
    return _d_0;
  }
}

function $Mine_start(_host_0, _c0_0, _c1_0) {
  if (_host_0) {
    return {$: "Con", "head": {$: "Held", "card": _c0_0, "pos": 0}, "tail": {$: "Con", "head": {$: "Held", "card": _c1_0, "pos": 1}, "tail": {$: "Nil"}}};
  } else {
    return {$: "Con", "head": {$: "Held", "card": _c0_0, "pos": 2}, "tail": {$: "Con", "head": {$: "Held", "card": _c1_0, "pos": 3}, "tail": {$: "Nil"}}};
  }
}

function $Mine_pos_pick(_hit_0, _p_0, _rest_0) {
  if (_hit_0) {
    return _p_0;
  } else {
    return _rest_0;
  }
}

function $Mine_pos(_hs_0, _c_0) {
  if (_hs_0.$ === "Nil") {
    return 99;
  } else {
    const _t_0 = _hs_0["head"];
    const _hc_0 = _t_0["card"];
    const _p_0 = _t_0["pos"];
    const _t_1 = _hs_0["tail"];
    return $Mine_pos_pick((_hc_0 === _c_0), _p_0, $$Mine_pos(_t_1, _c_0));
  }
}

function $Mine_keep(_drop_0, _h_0, _rest_0) {
  if (_drop_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $Mine_play(_hs_0, _c_0) {
  if (_hs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _hs_0["head"];
    const _hc_0 = _t_0["card"];
    const _p_0 = _t_0["pos"];
    const _t_1 = _hs_0["tail"];
    return $Mine_keep((_hc_0 === _c_0), {$: "Held", "card": _hc_0, "pos": _p_0}, $$Mine_play(_t_1, _c_0));
  }
}

function $api_new(_blue_key_0, _red_key_0) {
  return $start({$: "Setup", "blue_secret": $$Secret_of_key(_blue_key_0), "red_secret": $$Secret_of_key(_red_key_0)});
}

function $api_new_dealt(_starter_0, _b0_0, _b1_0, _r0_0, _r1_0, _t_0) {
  return $start_dealt($$Side_of_code(_starter_0), {$: "Deal", "blue": {$: "Con", "head": _b0_0, "tail": {$: "Con", "head": _b1_0, "tail": {$: "Nil"}}}, "red": {$: "Con", "head": _r0_0, "tail": {$: "Con", "head": _r1_0, "tail": {$: "Nil"}}}, "table": _t_0});
}

function $api_starter(_blue_coin_0, _red_coin_0) {
  return $Side_code($$Coin_side((_blue_coin_0 === 0), (_red_coin_0 === 0)));
}

function $code_at_checked(_at_0, _g_0) {
  if (_at_0.$ === "Some") {
    const _sq_0 = _at_0["value"];
    return $Pieces_code_at($$Game_pieces(_g_0), _sq_0);
  } else {
    return 0;
  }
}

function $api_cell(_g_0, _sq_0) {
  return $code_at_checked($$Cell_of_u32(_sq_0), _g_0);
}

function $api_hand(_g_0, _side_0, _i_0) {
  return $U32s_nth($$Game_hand(_g_0, $$Side_of_code(_side_0)), (_i_0 ));
}

function $api_table(_g_0) {
  return $Game_table(_g_0);
}

function $api_turn(_g_0) {
  return $Side_code($$Game_turn(_g_0));
}

function $api_outcome(_g_0) {
  return $Outcome_code($$Game_result(_g_0));
}

function $api_quiet(_g_0) {
  const _x_0 = $$Game_quiet(_g_0);
  return (_x_0 >>>0);
}

function $api_move_count(_g_0) {
  const _x_0 = $$Actions_len($$legal_moves(_g_0));
  return (_x_0 >>>0);
}

function $api_move(_g_0, _i_0) {
  return $Action_code($$Actions_nth($$legal_moves(_g_0), (_i_0 )));
}

function $is_legal_checked(_ok_0, _g_0, _code_0) {
  if (_ok_0) {
    return $sel($$is_legal(_g_0, $$Action_of_code(_code_0)), 1, 0);
  } else {
    return 0;
  }
}

function $api_is_legal(_g_0, _code_0) {
  return $is_legal_checked($$Action_valid_code(_code_0), _g_0, _code_0);
}

function $play_checked(_ok_0, _g_0, _code_0) {
  if (_ok_0) {
    return $play(_g_0, $$Action_of_code(_code_0));
  } else {
    return _g_0;
  }
}

function $api_play(_g_0, _code_0) {
  return $play_checked($$Action_valid_code(_code_0), _g_0, _code_0);
}

function $play_revealed_checked(_ok_0, _g_0, _code_0) {
  if (_ok_0) {
    return $play_revealed(_g_0, $$Action_of_code(_code_0));
  } else {
    return _g_0;
  }
}

function $api_play_revealed(_g_0, _code_0) {
  return $play_revealed_checked($$Action_valid_code(_code_0), _g_0, _code_0);
}

function $api_bot(_g_0, _level_0, _seed_0) {
  return $Action_code($$bot_decide($$view(_g_0, $$Game_turn(_g_0)), (_level_0 ), ((_seed_0 + 1) >>> 0)));
}

function $Chances_pack(_c_0) {
  const _b_0 = _c_0["blue"];
  const _r_0 = _c_0["red"];
  const _d_0 = _c_0["draws"];
  const _x_0 = (_b_0 >>>0);
  const _x_1 = (_r_0 >>>0);
  const _x_2 = (Math.imul(_x_0, 1000000) >>> 0);
  const _x_3 = (Math.imul(_x_1, 1000) >>> 0);
  const _x_4 = ((_x_2 + _x_3) >>> 0);
  const _x_5 = (_d_0 >>>0);
  return ((_x_4 + _x_5) >>> 0);
}

function $api_chances(_g_0, _viewer_0) {
  return $Chances_pack($$chances($$view(_g_0, $$Side_of_code(_viewer_0))));
}

function $api_card_step_count(_id_0) {
  const _x_0 = $$Steps_len($$card_steps(_id_0));
  return (_x_0 >>>0);
}

function $api_card_step(_id_0, _i_0) {
  return $Step_pack($$Steps_nth($$card_steps(_id_0), (_i_0 )));
}

function $api_msg_move(_code_0) {
  return $Message_encode({$: "Played", "move": $$Action_of_code(_code_0)});
}

function $api_msg_resign() {
  return $Message_encode({$: "Resign"});
}

function $api_msg_read(_s_0) {
  return $Message_code($$Message_decode(_s_0));
}

function $api_invite(_room_0) {
  return $Invite_encode({$: "Invite", "room": _room_0});
}

function $Cards_name_of_pick(_hit_0, _a_0, _b_0) {
  if (_hit_0) {
    return _a_0;
  } else {
    return _b_0;
  }
}

function $Cards_name_of(_cs_0, _id_0) {
  if (_cs_0.$ === "Nil") {
    return "";
  } else {
    const _t_0 = _cs_0["head"];
    const _cid_0 = _t_0["id"];
    const _n_0 = _t_0["name"];
    const _t_1 = _cs_0["tail"];
    return $Cards_name_of_pick((_cid_0 === _id_0), _n_0, $$Cards_name_of(_t_1, _id_0));
  }
}

function $api_card_name(_id_0) {
  return $Cards_name_of($$deck(), _id_0);
}

function $Reach_add_go(_skip_0, _c_0, _acc_0) {
  if (_skip_0) {
    return _acc_0;
  } else {
    return {$: "Con", "head": _c_0, "tail": _acc_0};
  }
}

function $Reach_add(_t_0, _acc_0) {
  if (_t_0.$ === "None") {
    return _acc_0;
  } else {
    const _c_0 = _t_0["value"];
    return $Reach_add_go($$Cells_has(_acc_0, _c_0), _c_0, _acc_0);
  }
}

function $Reach_targets($0, $1, $2, $3) {
  for (;;) {
    {
      const _sts_0 = $0;
      const _sq_0 = $1;
      const _side_0 = $2;
      const _acc_0 = $3;
      if (_sts_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _st_0 = _sts_0["head"];
        const _rest_0 = _sts_0["tail"];
        $0 = _rest_0;
        $1 = _sq_0;
        $2 = _side_0;
        $3 = $$Reach_add($$Step_target(_st_0, _sq_0, _side_0), _acc_0);
        continue;
      }
    }
  }
}

function $Reach_walk($0, $1, $2, $3, $4, $5) {
  for (;;) {
    {
      const _fuel_0 = $0;
      const _enough_0 = $1;
      const _queue_0 = $2;
      const _sts_0 = $3;
      const _side_0 = $4;
      const _seen_0 = $5;
      if (_fuel_0 == 0) {
        return _seen_0;
      } else {
        const _f_0 = (_fuel_0 - 1);
        if (_enough_0) {
          return _seen_0;
        } else {
          if (_queue_0.$ === "Nil") {
            return _seen_0;
          } else {
            const _sq_0 = _queue_0["head"];
            const _rest_0 = _queue_0["tail"];
            const _fresh_0 = $$Reach_targets(_sts_0, _sq_0, _side_0, _seen_0);
            const _x_0 = $$Cells_len(_fresh_0);
            const _x_1 = $$Cells_len(_seen_0);
            const _new_0 = $$Cells_take((_x_0 < _x_1 ? 0 : _x_0 - _x_1), _fresh_0);
            $0 = _f_0;
            $1 = $$Nat_is_ge($$Cells_len(_fresh_0), 8);
            $2 = $$Cells_append(_rest_0, _new_0);
            $3 = _sts_0;
            $4 = _side_0;
            $5 = _fresh_0;
            continue;
          }
        }
      }
    }
  }
}

function $Card_never_traps_go(_sqs_0, _sts_0, _side_0) {
  if (_sqs_0.$ === "Nil") {
    return true;
  } else {
    const _sq_0 = _sqs_0["head"];
    const _rest_0 = _sqs_0["tail"];
    return $Bool_and($$Nat_is_ge($$Cells_len($$Reach_walk(49, false, {$: "Con", "head": _sq_0, "tail": {$: "Nil"}}, _sts_0, _side_0, {$: "Con", "head": _sq_0, "tail": {$: "Nil"}})), 8), $$Card_never_traps_go(_rest_0, _sts_0, _side_0));
  }
}

function $Cards_never_trap(_cs_0) {
  if (_cs_0.$ === "Nil") {
    return true;
  } else {
    const _t_0 = _cs_0["head"];
    const _st_0 = _t_0["steps"];
    const _t_1 = _cs_0["tail"];
    return $Bool_and($$Bool_and($$Card_never_traps_go($$Cells_all(), _st_0, {$: "Blue"}), $$Card_never_traps_go($$Cells_all(), _st_0, {$: "Red"})), $$Cards_never_trap(_t_1));
  }
}

function $deck_never_traps() {
  return $Cards_never_trap($$deck());
}

function $api_deck_never_traps() {
  return $sel($$deck_never_traps(), 1, 0);
}

function $api_width() {
  return $W();
}

function $api_home(_side_0) {
  return $Cell_u32($$Side_home($$Side_of_code(_side_0)));
}

function $api_move_card(_code_0) {
  return $Action_card($$Action_of_code(_code_0));
}

function $api_move_from(_code_0) {
  return $Cell_u32($$Action_from($$Action_of_code(_code_0)));
}

function $api_move_to(_code_0) {
  return $Cell_u32($$to_of($$Action_of_code(_code_0)));
}

function $api_outcome_of(_g_0) {
  return $Game_result(_g_0);
}

function $api_chances_of(_g_0, _viewer_0) {
  return $chances($$view(_g_0, $$Side_of_code(_viewer_0)));
}

function $api_ending(_g_0) {
  return $ending(_g_0);
}

function $api_click(_g_0, _me_0, _card_0, _s_0, _sq_0) {
  return $click_api($$Cell_of_u32(_sq_0), _g_0, $$Side_of_code(_me_0), _card_0, _s_0);
}

function $api_play_move(_g_0, _card_0, _from_0, _to_0) {
  return $play(_g_0, $$Action_of_parts(_card_0, _from_0, _to_0));
}

function $api_move_code(_card_0, _from_0, _to_0) {
  return $Action_code($$Action_of_parts(_card_0, _from_0, _to_0));
}

function $api_token_count(_g_0) {
  const _x_0 = $$Tokens_len($$scene(_g_0));
  return (_x_0 >>>0);
}

function $api_token(_g_0, _i_0) {
  return $Token_pack($$Tokens_nth($$scene(_g_0), (_i_0 )));
}

function $api_proto_mine(_host_0, _i_0) {
  const _x_0 = $$Nats_nth($$Proto_mine($$Bool_not((_host_0 === 0))), (_i_0 ));
  return (_x_0 >>>0);
}

function $api_proto_handed(_host_0, _i_0) {
  const _x_0 = $$Nats_nth($$Proto_handed($$Bool_not((_host_0 === 0))), (_i_0 ));
  return (_x_0 >>>0);
}

function $api_opp_start(_host_0, _table_0) {
  return $Opp_start($$Bool_not((_host_0 === 0)), _table_0);
}

function $Proof_of(_has_0, _pos_0, _card_0) {
  if (_has_0) {
    return {$: "Opened", "pos": (_pos_0 ), "card": _card_0};
  } else {
    return {$: "NoProof"};
  }
}

function $api_opp_play(_o_0, _card_0, _has_proof_0, _pos_0, _opened_0) {
  return $Opp_play(_o_0, _card_0, $$Proof_of($$Bool_not((_has_proof_0 === 0)), _pos_0, _opened_0));
}

function $api_opp_i_played(_o_0, _card_0) {
  return $Opp_i_played(_o_0, _card_0);
}

function $api_mine_start(_host_0, _c0_0, _c1_0) {
  return $Mine_start($$Bool_not((_host_0 === 0)), _c0_0, _c1_0);
}

function $api_mine_pos(_hs_0, _card_0) {
  const _x_0 = $$Mine_pos(_hs_0, _card_0);
  return (_x_0 >>>0);
}

function $api_mine_play(_hs_0, _card_0) {
  return $Mine_play(_hs_0, _card_0);
}

function $api_proto_expected(_host_0, _step_0) {
  return $Proto_expected($$Bool_not((_host_0 === 0)), (_step_0 ));
}

function $api_proto_order(_host_0, _step_0, _kind_0) {
  return $Proto_order($$Bool_not((_host_0 === 0)), (_step_0 ), _kind_0);
}

function $api_proto_coin_ok(_matches_0, _bit_0) {
  return $sel($$Proto_coin_ok($$Bool_not((_matches_0 === 0)), _bit_0), 1, 0);
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}

function $Nat_is_le(_a_0, _b_0) {
  return $Cmp_is_le(cmp_new(_a_0, _b_0));
}

function $Bool_and(_a_0, _b_0) {
  if (!_a_0) {
    return false;
  } else {
    return _b_0;
  }
}

function $Nat_is_eq(_a_0, _b_0) {
  return $Cmp_is_eq(cmp_new(_a_0, _b_0));
}

function $U32_is_even(_a_0) {
  const _x_0 = ((_a_0 & 1) >>> 0);
  return (_x_0 === 0);
}

function $Nat_is_ge(_a_0, _b_0) {
  return $Cmp_is_ge(cmp_new(_a_0, _b_0));
}

function $Char_is_eq(_a_0, _b_0) {
  const _x_0 = char_code(_a_0);
  const _y_0 = char_code(_b_0);
  return (_x_0 === _y_0);
}

function $Cmp_is_le(_c_0) {
  if (_c_0.$ === "GT") {
    return false;
  } else {
    return true;
  }
}

function $Cmp_is_eq(_c_0) {
  if (_c_0.$ === "EQ") {
    return true;
  } else {
    return false;
  }
}

function $Cmp_is_ge(_c_0) {
  if (_c_0.$ === "LT") {
    return false;
  } else {
    return true;
  }
}

const $$U32s_has = $U32s_has;
const $$U32s_len = $U32s_len;
const $$U32s_count = $U32s_count;
const $$U32s_remove = $U32s_remove;
const $$U32s_replace = $U32s_replace;
const $$U32s_append = $U32s_append;
const $$U32s_range = $U32s_range;
const $$mix = $mix;
const $$U32s_sum_mix = $U32s_sum_mix;
const $$Fin7_nat = $Fin7_nat;
const $$Nat_is_le = $Nat_is_le;
const $$Nat_is_eq = $Nat_is_eq;
const $$Fin7_of_nat = $Fin7_of_nat;
const $$Cells_row = $Cells_row;
const $$Fin7s_all = $Fin7s_all;
const $$Cells_rows = $Cells_rows;
const $$Cell_eq = $Cell_eq;
const $$Cells_has = $Cells_has;
const $$Cells_len = $Cells_len;
const $$Cells_take = $Cells_take;
const $$Cells_append = $Cells_append;
const $$Side_is_blue = $Side_is_blue;
const $$Bool_not = $Bool_not;
const $$Bool_and = $Bool_and;
const $$Bool_same = $Bool_same;
const $$Fin7_shift = $Fin7_shift;
const $$Dist_nat = $Dist_nat;
const $$Shapes_steps = $Shapes_steps;
const $$Card_make = $Card_make;
const $$CardDefs_make = $CardDefs_make;
const $$deck_defs = $deck_defs;
const $$Step_same = $Step_same;
const $$Steps_has = $Steps_has;
const $$Step_reach = $Step_reach;
const $$Steps_max_reach = $Steps_max_reach;
const $$Cards_ids = $Cards_ids;
const $$Cards_len = $Cards_len;
const $$Cards_max_reach = $Cards_max_reach;
const $$Cards_steps_of = $Cards_steps_of;
const $$Steps_len = $Steps_len;
const $$sel = $sel;
const $$deck = $deck;
const $$CardDefs_nth = $CardDefs_nth;
const $$draw_pick = $draw_pick;
const $$rng = $rng;
const $$draw_n = $draw_n;
const $$U32s_rot1 = $U32s_rot1;
const $$Nats_head0 = $Nats_head0;
const $$Nats_tail = $Nats_tail;
const $$Draw_k = $Draw_k;
const $$U32s_rotate = $U32s_rotate;
const $$Draw_go = $Draw_go;
const $$U32_is_even = $U32_is_even;
const $$U32s_distinct = $U32s_distinct;
const $$U32s_all_in = $U32s_all_in;
const $$Piece_code = $Piece_code;
const $$Pieces_code_at = $Pieces_code_at;
const $$Side_same = $Side_same;
const $$Pieces_teacher_of = $Pieces_teacher_of;
const $$Pieces_len = $Pieces_len;
const $$Pieces_capture = $Pieces_capture;
const $$Cell_sel = $Cell_sel;
const $$Pieces_move = $Pieces_move;
const $$Cell_u32 = $Cell_u32;
const $$Pieces_key = $Pieces_key;
const $$Cell_of_u32 = $Cell_of_u32;
const $$Cell_or_corner = $Cell_or_corner;
const $$Action_of_code = $Action_of_code;
const $$Action_code = $Action_code;
const $$Action_same = $Action_same;
const $$Actions_has = $Actions_has;
const $$Actions_len = $Actions_len;
const $$Pieces_start = $Pieces_start;
const $$Game_key = $Game_key;
const $$Setup_starter = $Setup_starter;
const $$Setup_deal = $Setup_deal;
const $$Pieces_side_at = $Pieces_side_at;
const $$Step_target = $Step_target;
const $$gen_add_to = $gen_add_to;
const $$gen_pieces_one = $gen_pieces_one;
const $$card_steps = $card_steps;
const $$gen_pieces = $gen_pieces;
const $$Game_turn = $Game_turn;
const $$Game_hand = $Game_hand;
const $$Game_pieces = $Game_pieces;
const $$Game_result = $Game_result;
const $$Outcome_is_over = $Outcome_is_over;
const $$legal_moves = $legal_moves;
const $$U32s_nth = $U32s_nth;
const $$Nat_is_ge = $Nat_is_ge;
const $$Cell_is = $Cell_is;
const $$Side_home = $Side_home;
const $$Side_other = $Side_other;
const $$hand_after = $hand_after;
const $$quiet_after = $quiet_after;
const $$history_after = $history_after;
const $$Game_drawn = $Game_drawn;
const $$outcome_after = $outcome_after;
const $$won = $won;
const $$is_legal = $is_legal;
const $$play = $play;
const $$start = $start;
const $$outcome = $outcome;
const $$after = $after;
const $$Game_history = $Game_history;
const $$reveal_hand = $reveal_hand;
const $$with_enemy_hand = $with_enemy_hand;
const $$View_table = $View_table;
const $$View_own = $View_own;
const $$to_of = $to_of;
const $$find_win = $find_win;
const $$enemy_home = $enemy_home;
const $$enemy_teacher_square = $enemy_teacher_square;
const $$quick_move = $quick_move;
const $$is_over = $is_over;
const $$View_sample_enemy = $View_sample_enemy;
const $$View_guess = $View_guess;
const $$playout = $playout;
const $$Chances_add = $Chances_add;
const $$View_result = $View_result;
const $$View_key = $View_key;
const $$bot_points = $bot_points;
const $$View_side = $View_side;
const $$bot_score = $bot_score;
const $$bot_keep = $bot_keep;
const $$Actions_nth = $Actions_nth;
const $$Bit_char = $Bit_char;
const $$Bits_show = $Bits_show;
const $$Char_is_eq = $Char_is_eq;
const $$Bits_bit = $Bits_bit;
const $$Bits_read = $Bits_read;
const $$U32_of_bits = $U32_of_bits;
const $$U32_bits = $U32_bits;
const $$Bits_drop = $Bits_drop;
const $$Cell_of_maybe = $Cell_of_maybe;
const $$Cell_none = $Cell_none;
const $$Game_quiet = $Game_quiet;
const $$Action_card = $Action_card;
const $$Actions_with_card = $Actions_with_card;
const $$Actions_with_to = $Actions_with_to;
const $$Action_from = $Action_from;
const $$Actions_with_from = $Actions_with_from;
const $$click_moves = $click_moves;
const $$Action_of_parts = $Action_of_parts;
const $$click_api = $click_api;
const $$scene_of = $scene_of;
const $$Tokens_code_at = $Tokens_code_at;
const $$Tokens_len = $Tokens_len;
const $$Tokens_count = $Tokens_count;
const $$Tokens_cells = $Tokens_cells;
const $$Cells_unstacked = $Cells_unstacked;
const $$Nats_has = $Nats_has;
const $$Nats_without = $Nats_without;
const $$Proto_plan = $Proto_plan;
const $$Proto_index = $Proto_index;
const $$Proto_mine = $Proto_mine;
const $$Mine_pos = $Mine_pos;
const $$Mine_play = $Mine_play;
const $$Secret_of_key = $Secret_of_key;
const $$Side_of_code = $Side_of_code;
const $$Coin_side = $Coin_side;
const $$Action_valid_code = $Action_valid_code;
const $$view = $view;
const $$bot_decide = $bot_decide;
const $$chances = $chances;
const $$Steps_nth = $Steps_nth;
const $$Message_decode = $Message_decode;
const $$Cards_name_of = $Cards_name_of;
const $$Reach_add = $Reach_add;
const $$Reach_targets = $Reach_targets;
const $$Reach_walk = $Reach_walk;
const $$Card_never_traps_go = $Card_never_traps_go;
const $$Cells_all = $Cells_all;
const $$Cards_never_trap = $Cards_never_trap;
const $$deck_never_traps = $deck_never_traps;
const $$scene = $scene;
const $$Tokens_nth = $Tokens_nth;
const $$Nats_nth = $Nats_nth;
const $$Proto_handed = $Proto_handed;
const $$Proof_of = $Proof_of;
const $$Proto_coin_ok = $Proto_coin_ok;export default {
  "W": run_lib(() => run_loop($W()), 0),
  "NONE": run_lib(() => run_loop($NONE()), 0),
  "sel": run_lib((a0,a1,a2) => run_loop($sel(a0,a1,a2)), 3),
  "Bool.same": run_lib((a0,a1) => run_loop($Bool_same(a0,a1)), 2),
  "rng": run_lib((a0) => run_loop($rng(a0)), 1),
  "mix": run_lib((a0) => run_loop($mix(a0)), 1),
  "U32s.has": run_lib((a0,a1) => run_loop($U32s_has(a0,a1)), 2),
  "U32s.len": run_lib((a0) => run_loop($U32s_len(a0)), 1),
  "U32s.nth": run_lib((a0,a1) => run_loop($U32s_nth(a0,nat_in(a1))), 2),
  "U32s.count.add": run_lib((a0,a1) => run_loop($U32s_count_add(a0,nat_in(a1))), 2),
  "U32s.count": run_lib((a0,a1) => run_loop($U32s_count(a0,a1)), 2),
  "U32s.remove.go": run_lib((a0,a1,a2,a3) => run_loop($U32s_remove_go(a0,a1,a2,a3)), 4),
  "U32s.remove": run_lib((a0,a1) => run_loop($U32s_remove(a0,a1)), 2),
  "U32s.replace.go": run_lib((a0,a1,a2,a3,a4) => run_loop($U32s_replace_go(a0,a1,a2,a3,a4)), 5),
  "U32s.replace": run_lib((a0,a1,a2) => run_loop($U32s_replace(a0,a1,a2)), 3),
  "U32s.append": run_lib((a0,a1) => run_loop($U32s_append(a0,a1)), 2),
  "U32s.range": run_lib((a0) => run_loop($U32s_range(nat_in(a0))), 1),
  "U32s.sum_mix": run_lib((a0,a1) => run_loop($U32s_sum_mix(a0,a1)), 2),
  "Fin7.nat": run_lib((a0) => run_loop($Fin7_nat(a0)), 1),
  "Fin7.of_nat": run_lib((a0) => run_loop($Fin7_of_nat(nat_in(a0))), 1),
  "Fin7.down": run_lib((a0,a1,a2) => run_loop($Fin7_down(a0,nat_in(a1),nat_in(a2))), 3),
  "Fin7.shift": run_lib((a0,a1,a2) => run_loop($Fin7_shift(a0,nat_in(a1),a2)), 3),
  "Cell.eq": run_lib((a0,a1) => run_loop($Cell_eq(a0,a1)), 2),
  "Cell.sel": run_lib((a0,a1,a2) => run_loop($Cell_sel(a0,a1,a2)), 3),
  "Cell.is": run_lib((a0,a1) => run_loop($Cell_is(a0,a1)), 2),
  "Cell.none": run_lib((a0) => run_loop($Cell_none(a0)), 1),
  "Cell.both": run_lib((a0,a1) => run_loop($Cell_both(a0,a1)), 2),
  "Cell.u32": run_lib((a0) => run_loop($Cell_u32(a0)), 1),
  "Cell.of_u32": run_lib((a0) => run_loop($Cell_of_u32(a0)), 1),
  "Cell.or_corner": run_lib((a0) => run_loop($Cell_or_corner(a0)), 1),
  "Cell.code": run_lib((a0) => run_loop($Cell_code(a0)), 1),
  "Fin7s.all": run_lib(() => run_loop($Fin7s_all()), 0),
  "Cells.row": run_lib((a0,a1,a2) => run_loop($Cells_row(a0,a1,a2)), 3),
  "Cells.rows": run_lib((a0) => run_loop($Cells_rows(a0)), 1),
  "Cells.all": run_lib(() => run_loop($Cells_all()), 0),
  "Cells.has": run_lib((a0,a1) => run_loop($Cells_has(a0,a1)), 2),
  "Cells.len": run_lib((a0) => run_loop($Cells_len(a0)), 1),
  "Cells.take": run_lib((a0,a1) => run_loop($Cells_take(nat_in(a0),a1)), 2),
  "Cells.append": run_lib((a0,a1) => run_loop($Cells_append(a0,a1)), 2),
  "Side.other": run_lib((a0) => run_loop($Side_other(a0)), 1),
  "Side.is_blue": run_lib((a0) => run_loop($Side_is_blue(a0)), 1),
  "Side.of_bool": run_lib((a0) => run_loop($Side_of_bool(a0)), 1),
  "Side.of_code": run_lib((a0) => run_loop($Side_of_code(a0)), 1),
  "Side.same": run_lib((a0,a1) => run_loop($Side_same(a0,a1)), 2),
  "Side.code": run_lib((a0) => run_loop($Side_code(a0)), 1),
  "Side.home": run_lib((a0) => run_loop($Side_home(a0)), 1),
  "Step.mirror": run_lib((a0) => run_loop($Step_mirror(a0)), 1),
  "Step.flip": run_lib((a0) => run_loop($Step_flip(a0)), 1),
  "Step.is_vertical": run_lib((a0) => run_loop($Step_is_vertical(a0)), 1),
  "Step.same": run_lib((a0,a1) => run_loop($Step_same(a0,a1)), 2),
  "Step.reach": run_lib((a0) => run_loop($Step_reach(a0)), 1),
  "Step.target": run_lib((a0,a1,a2) => run_loop($Step_target(a0,a1,a2)), 3),
  "Dist.nat": run_lib((a0) => run_loop($Dist_nat(a0)), 1),
  "Shape.steps": run_lib((a0,a1) => run_loop($Shape_steps(a0,a1)), 2),
  "Shapes.steps": run_lib((a0) => run_loop($Shapes_steps(a0)), 1),
  "Card.make": run_lib((a0) => run_loop($Card_make(a0)), 1),
  "deck_defs": run_lib(() => run_loop($deck_defs()), 0),
  "CardDefs.make": run_lib((a0) => run_loop($CardDefs_make(a0)), 1),
  "CardDefs.nth": run_lib((a0,a1) => run_loop($CardDefs_nth(a0,nat_in(a1))), 2),
  "deck": run_lib(() => run_loop($deck()), 0),
  "Steps.has": run_lib((a0,a1) => run_loop($Steps_has(a0,a1)), 2),
  "Steps.max_reach": run_lib((a0) => run_loop($Steps_max_reach(a0)), 1),
  "Cards.ids": run_lib((a0) => run_loop($Cards_ids(a0)), 1),
  "Cards.len": run_lib((a0) => run_loop($Cards_len(a0)), 1),
  "Cards.max_reach": run_lib((a0) => run_loop($Cards_max_reach(a0)), 1),
  "Cards.steps_of.pick": run_lib((a0,a1,a2) => run_loop($Cards_steps_of_pick(a0,a1,a2)), 3),
  "Cards.steps_of": run_lib((a0,a1) => run_loop($Cards_steps_of(a0,a1)), 2),
  "Steps.len": run_lib((a0) => run_loop($Steps_len(a0)), 1),
  "Steps.nth": run_lib((a0,a1) => run_loop($Steps_nth(a0,nat_in(a1))), 2),
  "Step.pack": run_lib((a0) => run_loop($Step_pack(a0)), 1),
  "deck_size": run_lib(() => run_loop($deck_size()), 0),
  "deck_card": run_lib((a0) => run_loop($deck_card(nat_in(a0))), 1),
  "deck_max_step": run_lib(() => run_loop($deck_max_step()), 0),
  "card_has": run_lib((a0,a1) => run_loop($card_has(a0,a1)), 2),
  "card_steps": run_lib((a0) => run_loop($card_steps(a0)), 1),
  "Deal.hand_of": run_lib((a0,a1) => run_loop($Deal_hand_of(a0,a1)), 2),
  "U32s.nth_or": run_lib((a0,a1,a2) => run_loop($U32s_nth_or(a0,nat_in(a1),a2)), 3),
  "draw_pick": run_lib((a0,a1) => run_loop($draw_pick(a0,a1)), 2),
  "draw_n": run_lib((a0,a1,a2) => run_loop($draw_n(nat_in(a0),a1,a2)), 3),
  "Deal.of_list": run_lib((a0) => run_loop($Deal_of_list(a0)), 1),
  "Nats.head0": run_lib((a0) => run_loop($Nats_head0(a0)), 1),
  "Nats.tail": run_lib((a0) => run_loop($Nats_tail(a0)), 1),
  "U32s.rot1": run_lib((a0) => run_loop($U32s_rot1(a0)), 1),
  "U32s.rotate": run_lib((a0,a1) => run_loop($U32s_rotate(nat_in(a0),a1)), 2),
  "Draw.k": run_lib((a0,a1) => run_loop($Draw_k(a0,a1)), 2),
  "Draw.go": run_lib((a0,a1,a2,a3) => run_loop($Draw_go(nat_in(a0),a1,a2,a3)), 4),
  "deal_from": run_lib((a0,a1) => run_loop($deal_from(a0,a1)), 2),
  "Secret.of_key": run_lib((a0) => run_loop($Secret_of_key(a0)), 1),
  "U32s.distinct": run_lib((a0) => run_loop($U32s_distinct(a0)), 1),
  "U32s.all_in": run_lib((a0,a1) => run_loop($U32s_all_in(a0,a1)), 2),
  "Deal.five_ok": run_lib((a0) => run_loop($Deal_five_ok(a0)), 1),
  "Deal.is_valid": run_lib((a0) => run_loop($Deal_is_valid(a0)), 1),
  "Setup.deal": run_lib((a0) => run_loop($Setup_deal(a0)), 1),
  "Coin.side": run_lib((a0,a1) => run_loop($Coin_side(a0,a1)), 2),
  "Setup.starter": run_lib((a0) => run_loop($Setup_starter(a0)), 1),
  "Piece.code": run_lib((a0,a1) => run_loop($Piece_code(a0,a1)), 2),
  "Pieces.code_at": run_lib((a0,a1) => run_loop($Pieces_code_at(a0,a1)), 2),
  "Code.is_side": run_lib((a0,a1) => run_loop($Code_is_side(a0,a1)), 2),
  "Pieces.side_at": run_lib((a0,a1,a2) => run_loop($Pieces_side_at(a0,a1,a2)), 3),
  "Pieces.teacher_of.pick": run_lib((a0,a1,a2) => run_loop($Pieces_teacher_of_pick(a0,a1,a2)), 3),
  "Pieces.teacher_of": run_lib((a0,a1) => run_loop($Pieces_teacher_of(a0,a1)), 2),
  "Pieces.len": run_lib((a0) => run_loop($Pieces_len(a0)), 1),
  "Pieces.capture.go": run_lib((a0,a1,a2) => run_loop($Pieces_capture_go(a0,a1,a2)), 3),
  "Pieces.capture": run_lib((a0,a1,a2) => run_loop($Pieces_capture(a0,a1,a2)), 3),
  "Pieces.move": run_lib((a0,a1,a2) => run_loop($Pieces_move(a0,a1,a2)), 3),
  "Pieces.key": run_lib((a0) => run_loop($Pieces_key(a0)), 1),
  "Pieces.start": run_lib(() => run_loop($Pieces_start()), 0),
  "Outcome.is_win": run_lib((a0) => run_loop($Outcome_is_win(a0)), 1),
  "Outcome.is_over": run_lib((a0) => run_loop($Outcome_is_over(a0)), 1),
  "Outcome.code": run_lib((a0) => run_loop($Outcome_code(a0)), 1),
  "Action.card": run_lib((a0) => run_loop($Action_card(a0)), 1),
  "Action.from": run_lib((a0) => run_loop($Action_from(a0)), 1),
  "to_of": run_lib((a0) => run_loop($to_of(a0)), 1),
  "Action.same": run_lib((a0,a1) => run_loop($Action_same(a0,a1)), 2),
  "Action.code": run_lib((a0) => run_loop($Action_code(a0)), 1),
  "Action.of_code": run_lib((a0) => run_loop($Action_of_code(a0)), 1),
  "Action.valid_code": run_lib((a0) => run_loop($Action_valid_code(a0)), 1),
  "Actions.has": run_lib((a0,a1) => run_loop($Actions_has(a0,a1)), 2),
  "Actions.nonempty": run_lib((a0) => run_loop($Actions_nonempty(a0)), 1),
  "Actions.len": run_lib((a0) => run_loop($Actions_len(a0)), 1),
  "Actions.nth": run_lib((a0,a1) => run_loop($Actions_nth(a0,nat_in(a1))), 2),
  "Game.turn": run_lib((a0) => run_loop($Game_turn(a0)), 1),
  "Game.pieces": run_lib((a0) => run_loop($Game_pieces(a0)), 1),
  "Game.result": run_lib((a0) => run_loop($Game_result(a0)), 1),
  "Game.hand": run_lib((a0,a1) => run_loop($Game_hand(a0,a1)), 2),
  "Game.table": run_lib((a0) => run_loop($Game_table(a0)), 1),
  "Game.quiet": run_lib((a0) => run_loop($Game_quiet(a0)), 1),
  "Game.history": run_lib((a0) => run_loop($Game_history(a0)), 1),
  "Game.key": run_lib((a0,a1,a2,a3,a4) => run_loop($Game_key(a0,a1,a2,a3,a4)), 5),
  "start_dealt": run_lib((a0,a1) => run_loop($start_dealt(a0,a1)), 2),
  "start": run_lib((a0) => run_loop($start(a0)), 1),
  "gen.add": run_lib((a0,a1,a2) => run_loop($gen_add(a0,a1,a2)), 3),
  "gen.add_to": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($gen_add_to(a0,a1,a2,a3,a4,a5)), 6),
  "gen.steps": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($gen_steps(a0,a1,a2,a3,a4,a5)), 6),
  "gen.pieces.one": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($gen_pieces_one(a0,a1,a2,a3,a4,a5,a6)), 7),
  "gen.pieces": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($gen_pieces(a0,a1,a2,a3,a4,a5)), 6),
  "gen.cards": run_lib((a0,a1,a2,a3) => run_loop($gen_cards(a0,a1,a2,a3)), 4),
  "gen.if_ongoing": run_lib((a0,a1) => run_loop($gen_if_ongoing(a0,a1)), 2),
  "legal_moves": run_lib((a0) => run_loop($legal_moves(a0)), 1),
  "is_legal": run_lib((a0,a1) => run_loop($is_legal(a0,a1)), 2),
  "card_proven": run_lib((a0,a1) => run_loop($card_proven(a0,a1)), 2),
  "outcome_after": run_lib((a0,a1,a2) => run_loop($outcome_after(a0,a1,a2)), 3),
  "hand_after": run_lib((a0,a1,a2,a3) => run_loop($hand_after(a0,a1,a2,a3)), 4),
  "history_after": run_lib((a0,a1,a2) => run_loop($history_after(a0,a1,a2)), 3),
  "quiet_after": run_lib((a0,a1) => run_loop($quiet_after(a0,nat_in(a1))), 2),
  "Game.drawn": run_lib((a0,a1) => run_loop($Game_drawn(a0,nat_in(a1))), 2),
  "won": run_lib((a0,a1,a2) => run_loop($won(a0,a1,a2)), 3),
  "apply.go": run_lib((a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) => run_loop($apply_go(a0,a1,a2,a3,a4,a5,nat_in(a6),a7,a8,a9,a10)), 11),
  "apply": run_lib((a0,a1) => run_loop($apply(a0,a1)), 2),
  "play.go": run_lib((a0,a1,a2) => run_loop($play_go(a0,a1,a2)), 3),
  "play": run_lib((a0,a1) => run_loop($play(a0,a1)), 2),
  "replay": run_lib((a0,a1) => run_loop($replay(a0,a1)), 2),
  "after": run_lib((a0,a1) => run_loop($after(a0,a1)), 2),
  "turn_of": run_lib((a0) => run_loop($turn_of(a0)), 1),
  "outcome": run_lib((a0) => run_loop($outcome(a0)), 1),
  "is_over": run_lib((a0) => run_loop($is_over(a0)), 1),
  "has_winner": run_lib((a0) => run_loop($has_winner(a0)), 1),
  "repetitions": run_lib((a0,a1) => run_loop($repetitions(a0,a1)), 2),
  "quiet_turns": run_lib((a0,a1) => run_loop($quiet_turns(a0,a1)), 2),
  "has_legal_move": run_lib((a0) => run_loop($has_legal_move(a0)), 1),
  "card_count": run_lib((a0) => run_loop($card_count(a0)), 1),
  "piece_count": run_lib((a0) => run_loop($piece_count(a0)), 1),
  "enemy_home": run_lib((a0) => run_loop($enemy_home(a0)), 1),
  "enemy_teacher_square": run_lib((a0) => run_loop($enemy_teacher_square(a0)), 1),
  "enemy_at": run_lib((a0,a1) => run_loop($enemy_at(a0,a1)), 2),
  "own_at": run_lib((a0,a1) => run_loop($own_at(a0,a1)), 2),
  "own_cards": run_lib((a0,a1) => run_loop($own_cards(a0,a1)), 2),
  "table_card": run_lib((a0) => run_loop($table_card(a0)), 1),
  "with_enemy_hand": run_lib((a0,a1,a2) => run_loop($with_enemy_hand(a0,a1,a2)), 3),
  "reveal_hand.go": run_lib((a0,a1,a2) => run_loop($reveal_hand_go(a0,a1,a2)), 3),
  "reveal_hand": run_lib((a0,a1) => run_loop($reveal_hand(a0,a1)), 2),
  "play_revealed": run_lib((a0,a1) => run_loop($play_revealed(a0,a1)), 2),
  "View.make": run_lib((a0,a1,a2,a3,a4,a5,a6,a7,a8) => run_loop($View_make(a0,a1,a2,a3,a4,a5,nat_in(a6),a7,a8)), 9),
  "view": run_lib((a0,a1) => run_loop($view(a0,a1)), 2),
  "View.own": run_lib((a0) => run_loop($View_own(a0)), 1),
  "View.table": run_lib((a0) => run_loop($View_table(a0)), 1),
  "View.side": run_lib((a0) => run_loop($View_side(a0)), 1),
  "View.result": run_lib((a0) => run_loop($View_result(a0)), 1),
  "View.key": run_lib((a0) => run_loop($View_key(a0)), 1),
  "View.guess.go": run_lib((a0,a1,a2,a3,a4,a5,a6,a7,a8) => run_loop($View_guess_go(a0,a1,a2,a3,a4,a5,nat_in(a6),a7,a8)), 9),
  "View.guess": run_lib((a0,a1) => run_loop($View_guess(a0,a1)), 2),
  "View.sample_enemy": run_lib((a0,a1) => run_loop($View_sample_enemy(a0,a1)), 2),
  "find_win.pick": run_lib((a0,a1,a2) => run_loop($find_win_pick(a0,a1,a2)), 3),
  "find_win": run_lib((a0,a1,a2) => run_loop($find_win(a0,a1,a2)), 3),
  "quick_move.pick": run_lib((a0,a1,a2) => run_loop($quick_move_pick(a0,a1,a2)), 3),
  "quick_move": run_lib((a0,a1) => run_loop($quick_move(a0,a1)), 2),
  "playout": run_lib((a0,a1,a2,a3) => run_loop($playout(nat_in(a0),a1,a2,a3)), 4),
  "Chances.add": run_lib((a0,a1) => run_loop($Chances_add(a0,a1)), 2),
  "chances.run": run_lib((a0,a1,a2,a3) => run_loop($chances_run(nat_in(a0),a1,a2,a3)), 4),
  "chances.all": run_lib((a0,a1) => run_loop($chances_all(a0,nat_in(a1))), 2),
  "chances.go": run_lib((a0,a1,a2) => run_loop($chances_go(a0,a1,nat_in(a2))), 3),
  "chances_n": run_lib((a0,a1) => run_loop($chances_n(a0,nat_in(a1))), 2),
  "chances": run_lib((a0) => run_loop($chances(a0)), 1),
  "Chances.wins_of": run_lib((a0,a1) => run_loop($Chances_wins_of(a0,a1)), 2),
  "Chances.draws": run_lib((a0) => run_loop($Chances_draws(a0)), 1),
  "Chances.total": run_lib((a0) => run_loop($Chances_total(a0)), 1),
  "Chances.games": run_lib((a0) => run_loop($Chances_games(a0)), 1),
  "bot.points": run_lib((a0,a1) => run_loop($bot_points(a0,a1)), 2),
  "bot.score": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($bot_score(nat_in(a0),a1,a2,a3,a4,a5)), 6),
  "bot.keep": run_lib((a0,a1,a2) => run_loop($bot_keep(a0,a1,a2)), 3),
  "bot.best": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($bot_best(a0,nat_in(a1),a2,a3,a4,a5)), 6),
  "bot.by_level": run_lib((a0,a1,a2,a3) => run_loop($bot_by_level(nat_in(a0),a1,a2,a3)), 4),
  "bot.decide.go": run_lib((a0,a1,a2,a3,a4) => run_loop($bot_decide_go(a0,a1,a2,nat_in(a3),a4)), 5),
  "bot.decide": run_lib((a0,a1,a2) => run_loop($bot_decide(a0,nat_in(a1),a2)), 3),
  "Bit.char": run_lib((a0) => str_out(run_loop($Bit_char(a0))), 1),
  "Bits.show": run_lib((a0,a1,a2) => str_out(run_loop($Bits_show(nat_in(a0),a1,str_in(a2)))), 3),
  "Bits.bit.go": run_lib((a0,a1) => run_loop($Bits_bit_go(a0,a1)), 2),
  "Bits.bit": run_lib((a0) => run_loop($Bits_bit(str_in(a0))), 1),
  "Bits.cons": run_lib((a0,a1) => run_loop($Bits_cons(a0,a1)), 2),
  "Bits.read": run_lib((a0,a1) => run_loop($Bits_read(nat_in(a0),str_in(a1))), 2),
  "Bits.drop": run_lib((a0,a1) => str_out(run_loop($Bits_drop(nat_in(a0),str_in(a1)))), 2),
  "U32.bits": run_lib((a0,a1) => str_out(run_loop($U32_bits(a0,str_in(a1)))), 2),
  "U32.of_word": run_lib((a0) => run_loop($U32_of_word(a0)), 1),
  "U32.of_bits": run_lib((a0) => run_loop($U32_of_bits(str_in(a0))), 1),
  "Invite.encode": run_lib((a0) => str_out(run_loop($Invite_encode(a0))), 1),
  "Invite.of": run_lib((a0) => run_loop($Invite_of(a0)), 1),
  "Invite.decode": run_lib((a0) => run_loop($Invite_decode(str_in(a0))), 1),
  "Message.encode": run_lib((a0) => str_out(run_loop($Message_encode(a0))), 1),
  "Message.played": run_lib((a0,a1,a2) => run_loop($Message_played(a0,a1,a2)), 3),
  "Cell.of_maybe": run_lib((a0) => run_loop($Cell_of_maybe(a0)), 1),
  "Message.parse": run_lib((a0) => run_loop($Message_parse(str_in(a0))), 1),
  "Message.decode.resign": run_lib((a0) => run_loop($Message_decode_resign(str_in(a0))), 1),
  "Message.decode.go": run_lib((a0,a1,a2) => run_loop($Message_decode_go(a0,a1,str_in(a2))), 3),
  "Message.decode": run_lib((a0) => run_loop($Message_decode(str_in(a0))), 1),
  "Message.code": run_lib((a0) => run_loop($Message_code(a0)), 1),
  "ending.win": run_lib((a0) => run_loop($ending_win(a0)), 1),
  "ending.draw": run_lib((a0) => run_loop($ending_draw(a0)), 1),
  "ending.of": run_lib((a0,a1) => run_loop($ending_of(a0,a1)), 2),
  "ending": run_lib((a0) => run_loop($ending(a0)), 1),
  "Ending.is_over": run_lib((a0) => run_loop($Ending_is_over(a0)), 1),
  "Click.play": run_lib((a0) => run_loop($Click_play(a0)), 1),
  "Action.of_parts": run_lib((a0,a1,a2) => run_loop($Action_of_parts(a0,a1,a2)), 3),
  "Actions.keep": run_lib((a0,a1,a2) => run_loop($Actions_keep(a0,a1,a2)), 3),
  "Actions.with_card": run_lib((a0,a1) => run_loop($Actions_with_card(a0,a1)), 2),
  "Actions.with_to": run_lib((a0,a1) => run_loop($Actions_with_to(a0,a1)), 2),
  "Actions.with_from": run_lib((a0,a1) => run_loop($Actions_with_from(a0,a1)), 2),
  "click.moves": run_lib((a0,a1) => run_loop($click_moves(a0,a1)), 2),
  "click.select": run_lib((a0,a1,a2) => run_loop($click_select(a0,a1,a2)), 3),
  "click.crowd": run_lib((a0,a1) => run_loop($click_crowd(a0,a1)), 2),
  "click.one": run_lib((a0,a1,a2,a3) => run_loop($click_one(a0,a1,a2,a3)), 4),
  "click.reach": run_lib((a0,a1,a2) => run_loop($click_reach(a0,a1,a2)), 3),
  "click.free": run_lib((a0,a1,a2,a3,a4) => run_loop($click_free(a0,a1,a2,a3,a4)), 5),
  "click.go": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($click_go(a0,a1,a2,a3,a4,a5)), 6),
  "click": run_lib((a0,a1,a2,a3,a4) => run_loop($click(a0,a1,a2,a3,a4)), 5),
  "click.api": run_lib((a0,a1,a2,a3,a4) => run_loop($click_api(a0,a1,a2,a3,a4)), 5),
  "click_ok.of": run_lib((a0,a1,a2) => run_loop($click_ok_of(a0,a1,a2)), 3),
  "click_ok": run_lib((a0,a1,a2,a3,a4) => run_loop($click_ok(a0,a1,a2,a3,a4)), 5),
  "scene.of": run_lib((a0) => run_loop($scene_of(a0)), 1),
  "scene": run_lib((a0) => run_loop($scene(a0)), 1),
  "Tokens.code_at": run_lib((a0,a1) => run_loop($Tokens_code_at(a0,a1)), 2),
  "Tokens.len": run_lib((a0) => run_loop($Tokens_len(a0)), 1),
  "Tokens.count.add": run_lib((a0,a1) => run_loop($Tokens_count_add(a0,nat_in(a1))), 2),
  "Tokens.count": run_lib((a0,a1) => run_loop($Tokens_count(a0,a1)), 2),
  "Tokens.cells": run_lib((a0) => run_loop($Tokens_cells(a0)), 1),
  "Cells.unstacked": run_lib((a0) => run_loop($Cells_unstacked(a0)), 1),
  "Tokens.nth": run_lib((a0,a1) => run_loop($Tokens_nth(a0,nat_in(a1))), 2),
  "Token.pack": run_lib((a0) => run_loop($Token_pack(a0)), 1),
  "Nats.has": run_lib((a0,a1) => run_loop($Nats_has(a0,nat_in(a1))), 2),
  "Nats.keep": run_lib((a0,a1,a2) => run_loop($Nats_keep(a0,nat_in(a1),a2)), 3),
  "Nats.without": run_lib((a0,a1) => run_loop($Nats_without(a0,nat_in(a1))), 2),
  "Nats.nth": run_lib((a0,a1) => run_loop($Nats_nth(a0,nat_in(a1))), 2),
  "Proto.mine": run_lib((a0) => run_loop($Proto_mine(a0)), 1),
  "Proto.handed": run_lib((a0) => run_loop($Proto_handed(a0)), 1),
  "Proto.plan": run_lib((a0) => run_loop($Proto_plan(a0)), 1),
  "Proto.expected": run_lib((a0,a1) => run_loop($Proto_expected(a0,nat_in(a1))), 2),
  "Proto.index.pick": run_lib((a0,a1) => run_loop($Proto_index_pick(a0,nat_in(a1))), 2),
  "Proto.index": run_lib((a0,a1) => run_loop($Proto_index(a0,a1)), 2),
  "Order.is_cheat": run_lib((a0) => run_loop($Order_is_cheat(a0)), 1),
  "Proto.order.of": run_lib((a0) => run_loop($Proto_order_of(a0)), 1),
  "Proto.order.planned": run_lib((a0,a1,a2) => run_loop($Proto_order_planned(a0,nat_in(a1),nat_in(a2))), 3),
  "Proto.order.setup": run_lib((a0,a1) => run_loop($Proto_order_setup(nat_in(a0),nat_in(a1))), 2),
  "Proto.order.move": run_lib((a0) => run_loop($Proto_order_move(a0)), 1),
  "Proto.order.go": run_lib((a0,a1,a2,a3,a4) => run_loop($Proto_order_go(a0,a1,a2,nat_in(a3),a4)), 5),
  "Proto.order": run_lib((a0,a1,a2) => run_loop($Proto_order(a0,nat_in(a1),a2)), 3),
  "Proto.coin_ok": run_lib((a0,a1) => run_loop($Proto_coin_ok(a0,a1)), 2),
  "Opp.start": run_lib((a0,a1) => run_loop($Opp_start(a0,a1)), 2),
  "Opp.hidden": run_lib((a0) => run_loop($Opp_hidden(a0)), 1),
  "Opp.seen": run_lib((a0) => run_loop($Opp_seen(a0)), 1),
  "Opp.table": run_lib((a0) => run_loop($Opp_table(a0)), 1),
  "Opp.check": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($Opp_check(a0,nat_in(a1),a2,a3,a4,a5)), 6),
  "Opp.proof": run_lib((a0,a1,a2,a3,a4) => run_loop($Opp_proof(a0,a1,a2,a3,a4)), 5),
  "Opp.play.go": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($Opp_play_go(a0,a1,a2,a3,a4,a5)), 6),
  "Opp.play": run_lib((a0,a1,a2) => run_loop($Opp_play(a0,a1,a2)), 3),
  "Opp.i_played": run_lib((a0,a1) => run_loop($Opp_i_played(a0,a1)), 2),
  "Verdict.ok": run_lib((a0) => run_loop($Verdict_ok(a0)), 1),
  "Verdict.opp": run_lib((a0,a1) => run_loop($Verdict_opp(a0,a1)), 2),
  "Mine.start": run_lib((a0,a1,a2) => run_loop($Mine_start(a0,a1,a2)), 3),
  "Mine.pos.pick": run_lib((a0,a1,a2) => run_loop($Mine_pos_pick(a0,nat_in(a1),nat_in(a2))), 3),
  "Mine.pos": run_lib((a0,a1) => run_loop($Mine_pos(a0,a1)), 2),
  "Mine.keep": run_lib((a0,a1,a2) => run_loop($Mine_keep(a0,a1,a2)), 3),
  "Mine.play": run_lib((a0,a1) => run_loop($Mine_play(a0,a1)), 2),
  "api_new": run_lib((a0,a1) => run_loop($api_new(a0,a1)), 2),
  "api_new_dealt": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($api_new_dealt(a0,a1,a2,a3,a4,a5)), 6),
  "api_starter": run_lib((a0,a1) => run_loop($api_starter(a0,a1)), 2),
  "code_at.checked": run_lib((a0,a1) => run_loop($code_at_checked(a0,a1)), 2),
  "api_cell": run_lib((a0,a1) => run_loop($api_cell(a0,a1)), 2),
  "api_hand": run_lib((a0,a1,a2) => run_loop($api_hand(a0,a1,a2)), 3),
  "api_table": run_lib((a0) => run_loop($api_table(a0)), 1),
  "api_turn": run_lib((a0) => run_loop($api_turn(a0)), 1),
  "api_outcome": run_lib((a0) => run_loop($api_outcome(a0)), 1),
  "api_quiet": run_lib((a0) => run_loop($api_quiet(a0)), 1),
  "api_move_count": run_lib((a0) => run_loop($api_move_count(a0)), 1),
  "api_move": run_lib((a0,a1) => run_loop($api_move(a0,a1)), 2),
  "is_legal.checked": run_lib((a0,a1,a2) => run_loop($is_legal_checked(a0,a1,a2)), 3),
  "api_is_legal": run_lib((a0,a1) => run_loop($api_is_legal(a0,a1)), 2),
  "play.checked": run_lib((a0,a1,a2) => run_loop($play_checked(a0,a1,a2)), 3),
  "api_play": run_lib((a0,a1) => run_loop($api_play(a0,a1)), 2),
  "play_revealed.checked": run_lib((a0,a1,a2) => run_loop($play_revealed_checked(a0,a1,a2)), 3),
  "api_play_revealed": run_lib((a0,a1) => run_loop($api_play_revealed(a0,a1)), 2),
  "api_bot": run_lib((a0,a1,a2) => run_loop($api_bot(a0,a1,a2)), 3),
  "Chances.pack": run_lib((a0) => run_loop($Chances_pack(a0)), 1),
  "api_chances": run_lib((a0,a1) => run_loop($api_chances(a0,a1)), 2),
  "api_card_step_count": run_lib((a0) => run_loop($api_card_step_count(a0)), 1),
  "api_card_step": run_lib((a0,a1) => run_loop($api_card_step(a0,a1)), 2),
  "api_msg_move": run_lib((a0) => str_out(run_loop($api_msg_move(a0))), 1),
  "api_msg_resign": run_lib(() => str_out(run_loop($api_msg_resign())), 0),
  "api_msg_read": run_lib((a0) => run_loop($api_msg_read(str_in(a0))), 1),
  "api_invite": run_lib((a0) => str_out(run_loop($api_invite(a0))), 1),
  "Cards.name_of.pick": run_lib((a0,a1,a2) => str_out(run_loop($Cards_name_of_pick(a0,str_in(a1),str_in(a2)))), 3),
  "Cards.name_of": run_lib((a0,a1) => str_out(run_loop($Cards_name_of(a0,a1))), 2),
  "api_card_name": run_lib((a0) => str_out(run_loop($api_card_name(a0))), 1),
  "Reach.add.go": run_lib((a0,a1,a2) => run_loop($Reach_add_go(a0,a1,a2)), 3),
  "Reach.add": run_lib((a0,a1) => run_loop($Reach_add(a0,a1)), 2),
  "Reach.targets": run_lib((a0,a1,a2,a3) => run_loop($Reach_targets(a0,a1,a2,a3)), 4),
  "Reach.walk": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($Reach_walk(nat_in(a0),a1,a2,a3,a4,a5)), 6),
  "Card.never_traps.go": run_lib((a0,a1,a2) => run_loop($Card_never_traps_go(a0,a1,a2)), 3),
  "Cards.never_trap": run_lib((a0) => run_loop($Cards_never_trap(a0)), 1),
  "deck_never_traps": run_lib(() => run_loop($deck_never_traps()), 0),
  "api_deck_never_traps": run_lib(() => run_loop($api_deck_never_traps()), 0),
  "api_width": run_lib(() => run_loop($api_width()), 0),
  "api_home": run_lib((a0) => run_loop($api_home(a0)), 1),
  "api_move_card": run_lib((a0) => run_loop($api_move_card(a0)), 1),
  "api_move_from": run_lib((a0) => run_loop($api_move_from(a0)), 1),
  "api_move_to": run_lib((a0) => run_loop($api_move_to(a0)), 1),
  "api_outcome_of": run_lib((a0) => run_loop($api_outcome_of(a0)), 1),
  "api_chances_of": run_lib((a0,a1) => run_loop($api_chances_of(a0,a1)), 2),
  "api_ending": run_lib((a0) => run_loop($api_ending(a0)), 1),
  "api_click": run_lib((a0,a1,a2,a3,a4) => run_loop($api_click(a0,a1,a2,a3,a4)), 5),
  "api_play_move": run_lib((a0,a1,a2,a3) => run_loop($api_play_move(a0,a1,a2,a3)), 4),
  "api_move_code": run_lib((a0,a1,a2) => run_loop($api_move_code(a0,a1,a2)), 3),
  "api_token_count": run_lib((a0) => run_loop($api_token_count(a0)), 1),
  "api_token": run_lib((a0,a1) => run_loop($api_token(a0,a1)), 2),
  "api_proto_mine": run_lib((a0,a1) => run_loop($api_proto_mine(a0,a1)), 2),
  "api_proto_handed": run_lib((a0,a1) => run_loop($api_proto_handed(a0,a1)), 2),
  "api_opp_start": run_lib((a0,a1) => run_loop($api_opp_start(a0,a1)), 2),
  "Proof.of": run_lib((a0,a1,a2) => run_loop($Proof_of(a0,a1,a2)), 3),
  "api_opp_play": run_lib((a0,a1,a2,a3,a4) => run_loop($api_opp_play(a0,a1,a2,a3,a4)), 5),
  "api_opp_i_played": run_lib((a0,a1) => run_loop($api_opp_i_played(a0,a1)), 2),
  "api_mine_start": run_lib((a0,a1,a2) => run_loop($api_mine_start(a0,a1,a2)), 3),
  "api_mine_pos": run_lib((a0,a1) => run_loop($api_mine_pos(a0,a1)), 2),
  "api_mine_play": run_lib((a0,a1) => run_loop($api_mine_play(a0,a1)), 2),
  "api_proto_expected": run_lib((a0,a1) => run_loop($api_proto_expected(a0,a1)), 2),
  "api_proto_order": run_lib((a0,a1,a2) => run_loop($api_proto_order(a0,a1,a2)), 3),
  "api_proto_coin_ok": run_lib((a0,a1) => run_loop($api_proto_coin_ok(a0,a1)), 2),
};
