import Mathlib

/-!
# The Cayley-Dickson fold law: definitions + first targets
Conventions EXACTLY match the C++ code (`tower64.cpp`):
  (x, y) * (a, b) = (x*a - b*conj y, conj x * b + a*y)
  conj (x, y)     = (conj x, -y)
Level 0 = ℝ. `CD n` is an inductive tower so pattern matching reduces.
Targets (claims sheet T12): alternating art; ker L_z ≅ ker W; diagonal
blocks with C = -{L_x, L_y}; H = span{1,x,y,xy} ⊂ ker C; W|_H invertible;
direct sum x•(ker W) ⊓ H = ⊥; FOLD LAW dim ker (d+1) = 2·dim ker d + 4.
-/

namespace Foldlaw

/-- The Cayley-Dickson tower: level 0 is ℝ, each doubling pairs the level below. -/
inductive CD : ℕ → Type
  | zero : ℝ → CD 0
  | dbl : CD n → CD n → CD (n + 1)

open CD

/-- Componentwise negation. -/
def neg : ∀ {m : ℕ}, CD m → CD m
  | 0, zero r => zero (-r)
  | _ + 1, dbl x y => dbl (neg x) (neg y)

/-- Conjugation: trivial at level 0, (x, y)ᶜ = (xᶜ, -y) at each doubling. -/
def conj : ∀ {m : ℕ}, CD m → CD m
  | 0, zero r => zero r
  | _ + 1, dbl x y => dbl (conj x) (neg y)

/-- Componentwise addition (vector space structure). -/
def add : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r + s)
  | _ + 1, dbl x y, dbl a b => dbl (add x a) (add y b)

/-- Componentwise subtraction. -/
def sub : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r - s)
  | _ + 1, dbl x y, dbl a b => dbl (sub x a) (sub y b)

/-- CD multiplication (code convention): (x,y)*(a,b) = (x*a - b*yᶜ, xᶜ*b + a*y). -/
def mul : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r * s)
  | _ + 1, dbl x y, dbl a b =>
      dbl (sub (mul x a) (mul b (conj y))) (add (mul (conj x) b) (mul a y))

instance : Add (CD m) := ⟨add⟩
instance : Neg (CD m) := ⟨neg⟩
instance : Sub (CD m) := ⟨sub⟩
instance : HMul (CD m) (CD m) (CD m) := ⟨mul⟩

-- NOTE (honest scope): alternating art FAILS at levels >= 4 (sedenions are
-- not alternative). art_left / art_right as tower-wide statements are FALSE.
-- Correct reduction: associativity at level m implies art at level m+1.
-- Claims sheet: "H subset ker C by alternating art" closes for the tested
-- base pairs (check G: 930/930; there conj x * x = 1), not as a general law.

/- Target T1' (left art, honest form). NOTE (2026-10-01): associativity
alone is NOT enough -- expanding the successor step, the components reduce to
identities requiring the norm a * conj a and trace a + conj a to be CENTRAL
at level m (quadratic algebra, Schafer). These hold at levels 0-2 (R, C, H),
giving alternativity at level 3 (O) -- and failing beyond, where the art
indeed dies. The theorem itself lives near the end of the file, after the
lemmas its proof consumes (Lean needs no forward references). Same for T2'
(right art, honest form): same quadratic hypotheses. -/

/-- Double negation at every level. -/
theorem neg_neg {m : ℕ} (a : CD m) : neg (neg a) = a := by
  induction m with
  | zero => cases a; simp [neg]
  | succ n ih =>
    cases a with
    | dbl x y => simp [neg, ih]

/-- Conjugation is an involution at every level (needed everywhere in the
art expansion; base lemma of the fold-law chain). -/
theorem conj_conj {m : ℕ} (a : CD m) : conj (conj a) = a := by
  induction m with
  | zero => cases a; rfl
  | succ n ih =>
    cases a with
    | dbl x y => simp [conj, ih, neg_neg]

theorem add_comm {m : ℕ} (a b : CD m) : a + b = b + a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.add_comm r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem add_assoc {m : ℕ} (a b c : CD m) : a + b + c = a + (b + c) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t => exact congrArg zero (_root_.add_assoc r s t)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v =>
        cases c with
        | dbl p q => exact congrArg₂ dbl (ih x u p) (ih y v q)

theorem neg_add {m : ℕ} (a b : CD m) : neg (a + b) = neg a + neg b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.neg_add r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem conj_add {m : ℕ} (a b : CD m) : conj (a + b) = conj a + conj b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => rfl
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (neg_add y v)

theorem sub_add {m : ℕ} (a b : CD m) : a - b = a + neg b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.sub_eq_add_neg r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem sub_dist {m : ℕ} (a b c d : CD m) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t =>
          cases d with
          | zero w =>
            exact congrArg zero (show (r + s) - (t + w) = (r - t) + (s - w) by ring)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v =>
        cases c with
        | dbl p q =>
          cases d with
          | dbl w z =>
            exact congrArg₂ dbl (ih x u p w) (ih y v q z)

theorem add_four {m : ℕ} (P Q R S : CD m) :
    (P + Q) + (R + S) = (P + R) + (Q + S) := by
  rw [← add_assoc (P + Q) R S, add_assoc P Q R, add_comm Q R,
    add_assoc P (R + Q) S, add_assoc R Q S, ← add_assoc P R (Q + S)]

/-- Both distributivity laws, proved together (each uses the other in the
successor step). -/
theorem distrib {m : ℕ} (a b c : CD m) :
    a * (b + c) = a * b + a * c ∧ (b + c) * a = b * a + c * a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t =>
          constructor
          · exact congrArg zero (show r * (s + t) = r * s + r * t by ring)
          · exact congrArg zero (show (s + t) * r = s * r + t * r by ring)
  | succ n ih =>
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
cases c with
    | dbl c1 c2 =>
      have hL : ∀ a b c : CD n, a * (b + c) = a * b + a * c :=
        fun a b c => (ih a b c).1
      have hR : ∀ a b c : CD n, (b + c) * a = b * a + c * a :=
        fun a b c => (ih a b c).2
      have h1 : a1 * (b1 + c1) - (b2 + c2) * conj a2
          = (a1 * b1 - b2 * conj a2) + (a1 * c1 - c2 * conj a2) := by
        rw [hL a1 b1 c1, hR (conj a2) b2 c2, sub_dist]
      have h2 : conj a1 * (b2 + c2) + (b1 + c1) * a2
          = (conj a1 * b2 + b1 * a2) + (conj a1 * c2 + c1 * a2) := by
        rw [hL (conj a1) b2 c2, hR a2 b1 c1, add_four]
      have h3 : (b1 + c1) * a1 - a2 * conj (b2 + c2)
          = (b1 * a1 - a2 * conj b2) + (c1 * a1 - a2 * conj c2) := by
        rw [hR a1 b1 c1, conj_add b2 c2, hL a2 (conj b2) (conj c2), sub_dist]
      have h4 : conj (b1 + c1) * a2 + a1 * (b2 + c2)
          = (conj b1 * a2 + a1 * b2) + (conj c1 * a2 + a1 * c2) := by
        rw [conj_add b1 c1, hR a2 (conj b1) (conj c1), hL a1 b2 c2, add_four]
      constructor
      · exact congrArg₂ dbl h1 h2
      · exact congrArg₂ dbl h3 h4

theorem conj_neg {m : ℕ} (a : CD m) : conj (neg a) = neg (conj a) := by
  induction m with
  | zero => cases a with
    | zero r => rfl
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) rfl

/-- neg_mul and mul_neg proved together: each uses the other in the
successor step. -/
theorem neg_mul_mul_neg {m : ℕ} (a b : CD m) :
    neg a * b = neg (a * b) ∧ a * neg b = neg (a * b) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show -r * s = -(r * s) by ring)
        · exact congrArg zero (show r * -s = -(r * s) by ring)
  | succ n ih =>
    have hN : ∀ a b : CD n, neg a * b = neg (a * b) := fun a b => (ih a b).1
    have hM : ∀ a b : CD n, a * neg b = neg (a * b) := fun a b => (ih a b).2
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
        have h1 : neg a1 * b1 - b2 * conj (neg a2)
            = neg (a1 * b1 - b2 * conj a2) := by
          rw [hN a1 b1, conj_neg a2, hM b2 (conj a2), sub_add, sub_add,
            neg_add, neg_neg (b2 * conj a2)]
        have h2 : conj (neg a1) * b2 + b1 * neg a2
            = neg (conj a1 * b2 + b1 * a2) := by
          rw [conj_neg a1, hN (conj a1) b2, hM b1 a2, neg_add]
        have h3 : a1 * neg b1 - neg b2 * conj a2
            = neg (a1 * b1 - b2 * conj a2) := by
          rw [hM a1 b1, hN b2 (conj a2), sub_add, sub_add,
            neg_add, neg_neg (b2 * conj a2)]
        have h4 : conj a1 * neg b2 + neg b1 * a2
            = neg (conj a1 * b2 + b1 * a2) := by
          rw [hM (conj a1) b2, hN b1 a2, neg_add]
        constructor
        · exact congrArg₂ dbl h1 h2
        · exact congrArg₂ dbl h3 h4

theorem neg_mul {m : ℕ} (a b : CD m) : neg a * b = neg (a * b) :=
  (neg_mul_mul_neg a b).1

theorem mul_neg {m : ℕ} (a b : CD m) : a * neg b = neg (a * b) :=
  (neg_mul_mul_neg a b).2

/-- Conjugation is an anti-automorphism: conj (a * b) = conj b * conj a. -/
theorem conj_mul {m : ℕ} (a b : CD m) : conj (a * b) = conj b * conj a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (show r * s = s * r by ring)
  | succ n ih =>
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
        have h1 : conj (a1 * b1 - b2 * conj a2)
            = conj b1 * conj a1 - neg a2 * conj (neg b2) := by
          rw [sub_add, conj_add, conj_neg (b2 * conj a2), ih a1 b1,
            ih b2 (conj a2), conj_conj a2, conj_neg b2,
            neg_mul a2 (neg (conj b2)), mul_neg a2 (conj b2),
            neg_neg (a2 * conj b2), sub_add]
        have h2 : neg (conj a1 * b2 + b1 * a2)
            = conj (conj b1) * neg a2 + conj a1 * neg b2 := by
          rw [neg_add, conj_conj b1, mul_neg b1 a2, mul_neg (conj a1) b2,
            add_comm (neg (conj a1 * b2)) (neg (b1 * a2))]
        exact congrArg₂ dbl h1 h2

/-- The three quadratic hypotheses at level 0 (R): trivial, but these are
the base cases of the induction chain R -> C -> H that yields art at O. -/
theorem hassoc_zero (a b c : CD 0) : a * b * c = a * (b * c) := by
  cases a with
  | zero x =>
    cases b with
    | zero y =>
      cases c with
      | zero z =>
        exact congrArg zero (show x * y * z = x * (y * z) by ring)

theorem trace_central_zero (r c : CD 0) : (r + conj r) * c = c * (r + conj r) := by
  cases r with
  | zero x =>
    cases c with
    | zero y =>
      exact congrArg zero (show (x + x) * y = y * (x + x) by ring)

theorem norm_central_zero (r c : CD 0) : (r * conj r) * c = c * (r * conj r) := by
  cases r with
  | zero x =>
    cases c with
    | zero y =>
      exact congrArg zero (show (x * x) * y = y * (x * x) by ring)

/-- The zero of the tower (base of the identity-lemma block needed for the
hereditary step: conj_zero, zero_mul, mul_zero, add_zero, sub_self...). -/
def cdZero : ∀ {m : ℕ}, CD m
  | 0 => zero 0
  | _ + 1 => dbl cdZero cdZero

/-- The one of the tower: (1, 0, 0, ...) at every level. -/
def cdOne : ∀ {m : ℕ}, CD m
  | 0 => zero 1
  | _ + 1 => dbl cdOne cdZero

theorem neg_zero {m : ℕ} : neg (cdZero : CD m) = cdZero := by
  induction m with
  | zero => exact congrArg zero _root_.neg_zero
  | succ n ih => exact congrArg₂ dbl ih ih

theorem conj_zero {m : ℕ} : conj (cdZero : CD m) = cdZero := by
  induction m with
  | zero => rfl
  | succ n ih => exact congrArg₂ dbl ih neg_zero

theorem add_zero {m : ℕ} (a : CD m) : a + cdZero = a := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (_root_.add_zero r)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem zero_add {m : ℕ} (a : CD m) : cdZero + a = a := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (_root_.zero_add r)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem add_neg_self {m : ℕ} (a : CD m) : a + neg a = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (show r + -r = (0:ℝ) by ring)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem sub_self {m : ℕ} (a : CD m) : a - a = cdZero := by
  rw [sub_add, add_neg_self]

theorem zero_mul_mul_zero {m : ℕ} (a b : CD m) :
    (cdZero : CD m) * b = cdZero ∧ a * (cdZero : CD m) = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show (0:ℝ) * s = 0 by ring)
        · exact congrArg zero (show r * (0:ℝ) = 0 by ring)
  | succ n ih =>
    have hZ : ∀ b : CD n, cdZero * b = cdZero := fun b => (ih cdZero b).1
    have hM : ∀ a : CD n, a * cdZero = cdZero := fun a => (ih a cdZero).2
    cases a with
    | dbl p q =>
      cases b with
      | dbl u v =>
        have c1 : (cdZero : CD n) * u - v * conj (cdZero : CD n) = cdZero := by
          rw [hZ u, conj_zero, hM v, sub_self]
        have c2 : conj (cdZero : CD n) * v + u * (cdZero : CD n) = cdZero := by
          rw [conj_zero, hZ v, hM u, add_zero]
        have c3 : p * (cdZero : CD n) - (cdZero : CD n) * conj q = cdZero := by
          rw [hM p, hZ (conj q), sub_self]
        have c4 : conj p * (cdZero : CD n) + (cdZero : CD n) * q = cdZero := by
          rw [hM (conj p), hZ q, add_zero]
        constructor
        · exact congrArg₂ dbl c1 c2
        · exact congrArg₂ dbl c3 c4

theorem zero_mul {m : ℕ} (b : CD m) : (cdZero : CD m) * b = cdZero :=
  (zero_mul_mul_zero cdZero b).1

theorem mul_zero {m : ℕ} (a : CD m) : a * (cdZero : CD m) = cdZero :=
  (zero_mul_mul_zero a cdZero).2

theorem conj_one {m : ℕ} : conj (cdOne : CD m) = cdOne := by
  induction m with
  | zero => rfl
  | succ n ih => exact congrArg₂ dbl ih neg_zero

theorem sub_zero {m : ℕ} (a : CD m) : a - (cdZero : CD m) = a := by
  rw [sub_add, neg_zero, add_zero]

theorem one_mul_mul_one {m : ℕ} (a b : CD m) :
    (cdOne : CD m) * b = b ∧ a * (cdOne : CD m) = a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show (1:ℝ) * s = s by ring)
        · exact congrArg zero (show r * (1:ℝ) = r by ring)
  | succ n ih =>
    have h1 : ∀ b : CD n, (cdOne : CD n) * b = b := fun b => (ih cdOne b).1
    have h2 : ∀ a : CD n, a * (cdOne : CD n) = a := fun a => (ih a cdOne).2
    cases a with
    | dbl p q =>
      cases b with
      | dbl u v =>
        have c1 : (cdOne : CD n) * u - v * conj (cdZero : CD n) = u := by
          rw [h1 u, conj_zero, mul_zero, sub_zero]
        have c2 : conj (cdOne : CD n) * v + u * (cdZero : CD n) = v := by
          rw [conj_one, h1 v, mul_zero, add_zero]
        have c3 : p * (cdOne : CD n) - (cdZero : CD n) * conj q = p := by
          rw [h2 p, zero_mul, sub_zero]
        have c4 : conj p * (cdZero : CD n) + (cdOne : CD n) * q = q := by
          rw [mul_zero, h1 q, zero_add]
        constructor
        · exact congrArg₂ dbl c1 c2
        · exact congrArg₂ dbl c3 c4

theorem one_mul {m : ℕ} (b : CD m) : (cdOne : CD m) * b = b :=
  (one_mul_mul_one cdOne b).1

theorem mul_one {m : ℕ} (a : CD m) : a * (cdOne : CD m) = a :=
  (one_mul_mul_one a cdOne).2

/-- The central-pair bridge: an element (t, cdZero) with t fixed by
conjugation and central at level m commutes with EVERYTHING at level m+1.
This is the norm-to-centrality bridge the hereditary step consumes. -/
theorem real_pair_central {m : ℕ} (t u v : CD m)
    (hfix : conj t = t) (hcomm : ∀ c : CD m, t * c = c * t) :
    dbl t (cdZero : CD m) * dbl u v = dbl u v * dbl t (cdZero : CD m) := by
  have h1 : t * u - v * conj (cdZero : CD m)
      = u * t - (cdZero : CD m) * conj v := by
    rw [conj_zero, mul_zero, sub_zero, hcomm u, zero_mul, sub_zero]
  have h2 : conj t * v + u * (cdZero : CD m)
      = conj u * (cdZero : CD m) + t * v := by
    rw [hfix, mul_zero, add_zero, mul_zero, zero_add]
  exact congrArg₂ dbl h1 h2

/-- Hereditary step for the trace: if a + conj a is central at level m,
then x + conj x is central at level m+1 (every trace is a real pair
(t, cdZero), which real_pair_central makes commute with everything). -/
theorem trace_central_succ {m : ℕ}
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (x c : CD (m + 1)) : (x + conj x) * c = c * (x + conj x) := by
  cases x with
  | dbl p q =>
    cases c with
    | dbl u v =>
      show dbl (p + conj p) (q + neg q) * dbl u v
        = dbl u v * dbl (p + conj p) (q + neg q)
      rw [add_neg_self]
      exact real_pair_central (p + conj p) u v
        (by rw [conj_add, conj_conj, add_comm]) (htrace p)

theorem neg_add_self {m : ℕ} (a : CD m) : neg a + a = cdZero := by
  rw [add_comm, add_neg_self]

theorem mul_add' {m : ℕ} (a b c : CD m) : a * (b + c) = a * b + a * c :=
  (distrib a b c).1

theorem add_mul' {m : ℕ} (a b c : CD m) : (b + c) * a = b * a + c * a :=
  (distrib a b c).2

theorem central_add {m : ℕ} (t s : CD m)
    (ht : ∀ c : CD m, t * c = c * t) (hs : ∀ c : CD m, s * c = c * s) :
    ∀ c : CD m, (t + s) * c = c * (t + s) := by
  intro c
  rw [add_mul', mul_add', ht c, hs c]

/-- Hereditary step for the norm: if a * conj a is central at level m,
then x * conj x is central at level m+1 (the norm is the real pair
(p * conj p + q * conj q, cdZero), central as a sum of central elements). -/
theorem norm_central_succ {m : ℕ}
    (hnorm : ∀ a c : CD m, (a * conj a) * c = c * (a * conj a))
    (x c : CD (m + 1)) : (x * conj x) * c = c * (x * conj x) := by
  cases x with
  | dbl p q =>
    cases c with
    | dbl u v =>
      show dbl (p * conj p - neg q * conj q) (conj p * neg q + conj p * q)
          * dbl u v
        = dbl u v * dbl (p * conj p - neg q * conj q) (conj p * neg q + conj p * q)
      rw [neg_mul, sub_add, neg_neg, mul_neg, neg_add_self]
      exact real_pair_central (p * conj p + q * conj q) u v
        (by rw [conj_add, conj_mul q (conj q), conj_mul p (conj p), conj_conj q,
            conj_conj p, add_comm])
        (central_add (p * conj p) (q * conj q) (hnorm p) (hnorm q))

theorem comm_zero (a b : CD 0) : a * b = b * a := by
  cases a with
  | zero r =>
    cases b with
    | zero s => exact congrArg zero (show r * s = s * r by ring)

/-- Conjugation distributes over subtraction. -/
theorem conj_sub {m : ℕ} (a b : CD m) : conj (a - b) = conj a - conj b := by
  rw [sub_add, conj_add, conj_neg, ← sub_add]

/-- Left distribution of subtraction over multiplication. -/
theorem sub_mul {m : ℕ} (a b c : CD m) : (a - b) * c = a * c - b * c := by
  rw [sub_add, add_mul', neg_mul, ← sub_add]

/-- Right distribution of subtraction over multiplication. -/
theorem mul_sub {m : ℕ} (a b c : CD m) : a * (b - c) = a * b - a * c := by
  rw [sub_add, mul_add', mul_neg, ← sub_add]

/-- Additive shuffle consumed by the C1 alignment of `assoc_succ_of_comm`. -/
theorem sub_sub_add_shuffle {m : ℕ} (A B C D : CD m) :
    (A - B) - (C + D) = (A - C) - (D + B) := by
  rw [sub_add (A - B) (C + D), sub_add A B, sub_add (A - C) (D + B), sub_add A C,
      neg_add C D, neg_add D B, add_four A (neg B) (neg C) (neg D),
      add_comm (neg B) (neg D)]

/-- Additive shuffle consumed by the C2 alignment of `assoc_succ_of_comm`. -/
theorem sub_add_add_shuffle {m : ℕ} (A B C D : CD m) :
    (A - D) + (B + C) = (A + B) + (C - D) := by
  rw [sub_add A D, sub_add C D, add_four A (neg D) B C, add_comm (neg D) C]

/-- Left cancellation in the additive group (base of the norm-flip argument:
from (a + ā) * a = a * (a + ā) cancel a * a and get ā * a = a * ā). -/
theorem add_left_cancel' {m : ℕ} {A B C : CD m} (h : A + B = A + C) : B = C := by
  have h1 : neg A + (A + B) = neg A + (A + C) := congrArg (fun t => neg A + t) h
  rw [← add_assoc, neg_add_self, zero_add, ← add_assoc, neg_add_self, zero_add] at h1
  exact h1

/-- Right rotation of a 3-sum: A + (B + C) = C + (A + B). -/
theorem add_rot3 {m : ℕ} (A B C : CD m) : A + (B + C) = C + (A + B) := by
  rw [← add_assoc A B C, add_comm (A + B) C]

/-- Structural shuffle consumed by C1 of `art_left_of_assoc`: with Z = W and
X + Y = R + S, the nested difference aligns with the grouped difference. -/
theorem art_sub_shuffle {m : ℕ} (P X Y Z W R S : CD m)
    (h1 : Z = W) (h2 : X + Y = R + S) :
    (P - X) - (Y + Z) = (P - W) - (R + S) := by
  rw [h1, ← h2,
      sub_add (P - X) (Y + W), sub_add P X, neg_add Y W,
      add_assoc P (neg X) (neg Y + neg W),
      sub_add (P - W) (X + Y), sub_add P W, neg_add X Y,
      add_assoc P (neg W) (neg X + neg Y),
      add_rot3 (neg X) (neg Y) (neg W)]

/-- Structural shuffle consumed by C2 of `art_left_of_assoc`. -/
theorem art_pair_shuffle {m : ℕ} (A B C D E F G : CD m)
    (h1 : D = E) (h2 : B + C = F + G) :
    (A + B) + (C - D) = (A - E) + (F + G) := by
  rw [h1, sub_add C E, add_assoc A B (C + neg E), ← add_assoc B C (neg E), h2,
      sub_add A E, add_assoc A (neg E) (F + G), add_comm (F + G) (neg E)]

/-- Target: associativity lifts from a COMMUTATIVE associative level to the
next level. NOTE (2026-10-01, paper check): associativity alone does NOT lift
-- H -> O is the counterexample (H associative, O not) -- commutativity at
level m is required. Hence R (comm+assoc) -> C (assoc) -> H (assoc), and the
chain stops exactly where the art stops.

PROOF MAP (paper, 2026-10-01): with x = (p,q), y = (u,v), z = (w,s),
both sides reduce to 4-term sums; align term by term via hC then hA:
  C1: (p*u - v*qbar)*w - s*(vbar*p + qbar*ubar)  vs
      p*(u*w - s*vbar) - (ubar*s + w*v)*qbar
    - p*u*w  =  p*u*w  (identical)
    - v*qbar*w  =  w*v*qbar  : (w*v)=(v*w) [hC], (v*w)*qbar = v*(w*qbar) [hA],
      w*qbar = qbar*w [hC], v*(qbar*w) = (v*qbar)*w [hA]
    - s*vbar*p  =  p*s*vbar  : (s*vbar)*p = p*(s*vbar) [hC] = (p*s)*vbar [hA]
    - s*qbar*ubar  =  ubar*s*qbar  : (s*qbar)*ubar = ubar*(s*qbar) [hC]
      = (ubar*s)*qbar [hA]
  C2: (ubar*pbar - q*vbar)*s + w*(pbar*v + u*q)  vs
      pbar*(ubar*s + w*v) + (u*w - s*vbar)*q
    same dance: extract with sub_add/add_mul'/mul_add'/neg_mul, align with
    hC-then-hA, close with sub_zero/add_zero.
Tactic pattern: split each side into named 4-term haves, rewrite with
EXPLICIT instances (rw with metavars rewrites first match only).
Instantiation: comm_zero + hassoc_zero give m=0 (C associative); m=1 (H). -/
theorem assoc_succ_of_comm {m : ℕ}
    (hA : ∀ a b c : CD m, a * b * c = a * (b * c))
    (hC : ∀ a b : CD m, a * b = b * a)
    (x y z : CD (m + 1)) : x * y * z = x * (y * z) := by
  cases x with
  | dbl p q =>
    cases y with
    | dbl u v =>
      cases z with
      | dbl w s =>
        -- C1: first components. Normalize conj on both sides, expand the
        -- products, then align term by term hC-then-hA exactly as in the map.
        have hC1 : (p * u - v * conj q) * w - s * conj (conj p * v + u * q)
            = p * (u * w - s * conj v) - (conj u * s + w * v) * conj q := by
          rw [conj_add (conj p * v) (u * q), conj_mul (conj p) v, conj_mul u q,
              conj_conj p,
              sub_mul (p * u) (v * conj q) w,
              mul_add' s (conj v * p) (conj q * conj u),
              ← hA s (conj v) p, ← hA s (conj q) (conj u),
              mul_sub p (u * w) (s * conj v),
              ← hA p u w, ← hA p s (conj v),
              add_mul' (conj q) (conj u * s) (w * v),
              hA v (conj q) w, hC (conj q) w, ← hA v w (conj q), hC v w,
              hC (s * conj v) p, ← hA p s (conj v),
              hC (s * conj q) (conj u), ← hA (conj u) s (conj q),
              sub_sub_add_shuffle (p * u * w) (w * v * conj q)
                (p * s * conj v) (conj u * s * conj q)]
        -- C2: second components. Same dance: conj-normalize, expand, align.
        have hC2 : conj (p * u - v * conj q) * s + w * (conj p * v + u * q)
            = conj p * (conj u * s + w * v) + (u * w - s * conj v) * q := by
          rw [conj_sub (p * u) (v * conj q), conj_mul p u, conj_mul v (conj q),
              conj_conj q,
              sub_mul (conj u * conj p) (q * conj v) s,
              mul_add' w (conj p * v) (u * q),
              ← hA w (conj p) v, ← hA w u q,
              mul_add' (conj p) (conj u * s) (w * v),
              ← hA (conj p) (conj u) s, ← hA (conj p) w v,
              sub_mul (u * w) (s * conj v) q,
              hC (conj u) (conj p),
              hC (q * conj v) s, hC q (conj v), ← hA s (conj v) q,
              hC w (conj p), hC w u,
              sub_add_add_shuffle (conj p * conj u * s) (conj p * w * v)
                (u * w * q) (s * conj v * q)]
        exact congrArg₂ dbl hC1 hC2

/-- Instantiation m=0: ℂ (CD 1) is associative, from ℝ commutative+associative. -/
theorem assoc_one (x y z : CD 1) : x * y * z = x * (y * z) :=
  assoc_succ_of_comm hassoc_zero comm_zero x y z

/-- ℂ is commutative: at level 0 conjugation is the identity, so both
components reduce to commutativity of ℝ. This is the last rung where
commutativity holds -- ℍ kills it, and the chain stops with the art. -/
theorem comm_one (x y : CD 1) : x * y = y * x := by
  have hconj : ∀ t : CD 0, conj t = t := fun t => by cases t with | zero r => rfl
  cases x with
  | dbl a b =>
    cases y with
    | dbl c d =>
      have k1 : a * c - d * conj b = c * a - b * conj d := by
        rw [hconj b, hconj d, comm_zero a c, comm_zero d b]
      have k2 : conj a * d + c * b = conj c * b + a * d := by
        rw [hconj a, hconj c, add_comm (a * d) (c * b)]
      exact congrArg₂ dbl k1 k2

/-- Instantiation m=1: ℍ (CD 2) is associative. -/
theorem assoc_two (x y z : CD 2) : x * y * z = x * (y * z) :=
  assoc_succ_of_comm assoc_one comm_one x y z

/-!
### The honest art (T1'/T2')

Associativity at level m does NOT lift to the double (H → O is the
counterexample); what lifts, given a QUADRATIC level m (trace and norm
central, Schafer), is the art. Expansion with x = (p,q), w = (u,v) and the
code convention (x,y)*(a,b) = (x*a - b*ȳ, x̄*b + a*y):

  C1: p*(p*u - v*q̄) - (p̄*v + u*q)*q̄ = (p*p - q*q̄)*u - v*(q̄*p + q̄*p̄)
      - p*p*u identical on both sides;
      - p*v*q̄ + p̄*v*q̄ = (p + p̄)*v*q̄ = (v*q̄)*(p + p̄) = v*q̄*p + v*q̄*p̄
        (reassociate, then TRACE centrality `htrace p`);
      - u*q*q̄ = u*(q*q̄) = (q*q̄)*u (NORM centrality `hnorm q`).
  C2: p̄*(p̄*v + u*q) + (p*u - v*q̄)*q = (p̄*p̄ - q*q̄)*v + u*(p̄*q + p*q)
      - p̄*p̄*v identical;
      - p̄*(u*q) + p*(u*q) = (p̄ + p)*(u*q) = (u*(p̄ + p))*q = u*p̄*q + u*p*q
        (flipped trace centrality, from `htrace (conj p)` via conj_conj);
      - v*q̄*q = v*(q̄*q) = v*(q*q̄) = (q*q̄)*v (norm flip q̄*q = q*q̄ first,
        itself derived from `htrace` by additive cancellation).
-/

/-- Target T1' (left art, honest form): a quadratic associative level m
(central trace and norm) doubles into a left-alternative level m+1. -/
theorem art_left_of_assoc {m : ℕ}
    (hassoc : ∀ a b c : CD m, a * b * c = a * (b * c))
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (hnorm : ∀ a c : CD m, a * conj a * c = c * (a * conj a))
    (x w : CD (m + 1)) : x * (x * w) = (x * x) * w := by
  -- Norm flip: ā * a = a * ā, by cancelling a * a from the trace law on a.
  have hnormflip : ∀ a : CD m, conj a * a = a * conj a := by
    intro a
    have h : (a + conj a) * a = a * (a + conj a) := htrace a a
    rw [add_mul', mul_add'] at h
    exact add_left_cancel' h
  cases x with
  | dbl p q =>
    cases w with
    | dbl u v =>
      -- The flipped trace conj p + p is central: htrace (conj p) + conj_conj.
      have hpivot : ∀ c : CD m, (conj p + p) * c = c * (conj p + p) := by
        intro c
        have h := htrace (conj p) c
        rw [conj_conj p] at h
        exact h
      -- C1 pivots.
      have tpiv : (p + conj p) * v * conj q = v * conj q * (p + conj p) := by
        rw [hassoc (p + conj p) v (conj q), htrace p (v * conj q)]
      have npiv : u * q * conj q = q * conj q * u := by
        rw [hassoc u q (conj q), ← hnorm q u]
      have Lgrp : p * v * conj q + conj p * v * conj q
          = (p + conj p) * v * conj q := by
        rw [← add_mul' (conj q) (p * v) (conj p * v), ← add_mul' v p (conj p)]
      have Rgrp : v * conj q * p + v * conj q * conj p
          = v * conj q * (p + conj p) := by
        rw [← mul_add' (v * conj q) p (conj p)]
      have mid1 : p * v * conj q + conj p * v * conj q
          = v * conj q * p + v * conj q * conj p := by
        rw [Lgrp, tpiv, Rgrp]
      -- C2 pivots.
      have tpiv2 : (conj p + p) * (u * q) = (u * (conj p + p)) * q := by
        rw [← hassoc (conj p + p) u q, hpivot u]
      have npiv2 : v * conj q * q = q * conj q * v := by
        rw [hassoc v (conj q) q, hnormflip q, ← hnorm q v]
      have mid2 : conj p * (u * q) + p * (u * q)
          = u * conj p * q + u * p * q := by
        rw [← add_mul' (u * q) (conj p) p, tpiv2,
            ← add_mul' q (u * conj p) (u * p), ← mul_add' u (conj p) p]
      -- Component equalities, stated EXACTLY as the definitional expansion
      -- of the goal components so `congrArg₂ dbl` applies.
      have k1 : p * (p * u - v * conj q) - (conj p * v + u * q) * conj q
          = (p * p - q * conj q) * u - v * conj (conj p * q + p * q) := by
        rw [conj_add (conj p * q) (p * q), conj_mul (conj p) q, conj_mul p q,
            conj_conj p,
            mul_sub p (p * u) (v * conj q),
            ← hassoc p p u, ← hassoc p v (conj q),
            add_mul' (conj q) (conj p * v) (u * q),
            sub_mul (p * p) (q * conj q) u,
            mul_add' v (conj q * p) (conj q * conj p),
            ← hassoc v (conj q) p, ← hassoc v (conj q) (conj p),
            art_sub_shuffle (p * p * u) (p * v * conj q) (conj p * v * conj q)
              (u * q * conj q) (q * conj q * u) (v * conj q * p)
              (v * conj q * conj p) npiv mid1]
      have k2 : conj p * (conj p * v + u * q) + (p * u - v * conj q) * q
          = conj (p * p - q * conj q) * v + u * (conj p * q + p * q) := by
        rw [conj_sub (p * p) (q * conj q), conj_mul p p, conj_mul q (conj q),
            conj_conj q,
            mul_add' (conj p) (conj p * v) (u * q), ← hassoc (conj p) (conj p) v,
            sub_mul (p * u) (v * conj q) q, hassoc p u q,
            sub_mul (conj p * conj p) (q * conj q) v,
            mul_add' u (conj p * q) (p * q), ← hassoc u (conj p) q,
            ← hassoc u p q,
            art_pair_shuffle (conj p * conj p * v) (conj p * (u * q))
              (p * (u * q)) (v * conj q * q) (q * conj q * v) (u * conj p * q)
              (u * p * q) npiv2 mid2]
      exact congrArg₂ dbl k1 k2

/-- Target T2' (right art, honest form): mirror of the left art, obtained by
conjugating the goal and applying the left art at the conjugates. -/
theorem art_right_of_assoc {m : ℕ}
    (hassoc : ∀ a b c : CD m, a * b * c = a * (b * c))
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (hnorm : ∀ a c : CD m, a * conj a * c = c * (a * conj a))
    (w x : CD (m + 1)) : (w * x) * x = w * (x * x) := by
  rw [← conj_conj ((w * x) * x),
      conj_mul (w * x) x, conj_mul w x,
      art_left_of_assoc hassoc htrace hnorm (conj x) (conj w),
      conj_mul (conj x * conj x) (conj w),
      conj_mul (conj x) (conj x),
      conj_conj w, conj_conj x]

/-!
### The chain R → C → H → O, instantiated

ℝ (level 0) is commutative and associative, with trivially central trace and
norm. Each rung consumes exactly what the rungs below produce: C associative;
C commutative (the last commutative rung); H associative; H quadratic. The
payoff: the octonions (CD 3) are alternative.
-/

theorem trace_central_one (x c : CD 1) : (x + conj x) * c = c * (x + conj x) :=
  trace_central_succ trace_central_zero x c

theorem norm_central_one (x c : CD 1) : (x * conj x) * c = c * (x * conj x) :=
  norm_central_succ norm_central_zero x c

theorem trace_central_two (x c : CD 2) : (x + conj x) * c = c * (x + conj x) :=
  trace_central_succ trace_central_one x c

theorem norm_central_two (x c : CD 2) : (x * conj x) * c = c * (x * conj x) :=
  norm_central_succ norm_central_one x c

/-- ℍ is quadratic: associative with central trace and norm. The doubling of
a quadratic algebra is left-alternative -- this is the octonion case. -/
theorem art_left_three (x w : CD 3) : x * (x * w) = (x * x) * w :=
  art_left_of_assoc assoc_two trace_central_two norm_central_two x w

/-- Right-alternativity of the octonions, same hypotheses. -/
theorem art_right_three (w x : CD 3) : (w * x) * x = w * (x * x) :=
  art_right_of_assoc assoc_two trace_central_two norm_central_two w x

/-!
### Chain step (1) of the fold law: ker L_z ≅ ker W

With the code convention z*w = (x*a - b*ȳ, x̄*b + a*y) for z = (x, y),
w = (a, b), the system ker L_z reduces exactly to
(I) b = (x*a)*y and (II) W(a) = (x*a)*y + x*(a*y) = 0, where W is the
ANTI-ASSOCIATOR (claims sheet T12, hand derivation). The derivation uses the
art ONLY through two specific instances -- the left art in x and the right
art in y -- which is what lets the tower consume this theorem level after
level, long after global alternativity is dead.
-/

/-- From a - b = 0, recover a = b. -/
theorem sub_eq_zero {m : ℕ} {a b : CD m} (h : a - b = cdZero) : a = b := by
  have h1 : (a - b) + b = cdZero + b := congrArg (fun t => t + b) h
  rw [sub_add, add_assoc, neg_add_self, add_zero, zero_add] at h1
  exact h1

/-- From A + B = 0, recover B = -A. -/
theorem add_eq_zero_iff_neg {m : ℕ} {A B : CD m} (h : A + B = cdZero) :
    B = neg A := by
  have h1 : neg A + (A + B) = neg A + cdZero := congrArg (fun t => neg A + t) h
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at h1
  exact h1

/-- **Chain step (1).** For imaginary units x, y at level m satisfying the
left art in x and the right art in y, the kernel of left multiplication by
z = (x, y) at level m+1 is an exact copy of the kernel of the
anti-associator W(a) = (x*a)*y + x*(a*y): the pair (a, b) is killed by L_z
iff b is the determined image (x*a)*y and W kills a. -/
theorem ker_Lz_iff_ker_W {m : ℕ} (x y : CD m)
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y))
    (hx : conj x = neg x) (hy : conj y = neg y)
    (hx2 : x * x = neg (cdOne : CD m)) (hy2 : y * y = neg (cdOne : CD m))
    (a b : CD m) :
    dbl x y * dbl a b = (cdZero : CD (m + 1)) ↔
    b = (x * a) * y ∧ (x * a) * y + x * (a * y) = (cdZero : CD m) := by
  constructor
  · intro h
    have h' : dbl (x * a - b * conj y) (conj x * b + a * y)
        = (dbl (cdZero : CD m) (cdZero : CD m) : CD (m + 1)) := h
    injection h' with hidx h1 h2
    -- (I): right-multiply the first component by y (conj y = -y, right art).
    have e1 : (x * a) * y = (b * conj y) * y := by rw [sub_eq_zero h1]
    rw [hy, mul_neg, neg_mul, hartRy b, hy2, mul_neg, mul_one, neg_neg] at e1
    have hI : b = (x * a) * y := e1.symm
    -- (II): left-multiply the second component by x (conj x = -x, left art).
    have h2' : a * y + conj x * b = cdZero := by rw [add_comm, h2]
    have e2 : x * (conj x * b) = x * (neg (a * y)) :=
      by rw [add_eq_zero_iff_neg h2']
    rw [hx, neg_mul, mul_neg, hartLx b, hx2, neg_mul, one_mul, neg_neg, mul_neg] at e2
    have hII : (x * a) * y + x * (a * y) = cdZero := by
      rw [← hI, e2, neg_add_self]
    exact ⟨hI, hII⟩
  · rintro ⟨hI, hII⟩
    -- The image formula turns x*b into the left art in x: x*b = a*y.
    have hB : (x * a) * y = neg (x * (a * y)) :=
      add_eq_zero_iff_neg (by rw [add_comm, hII])
    have hxb : x * b = a * y := by
      rw [hI, hB, mul_neg, hartLx (a * y), hx2, neg_mul, one_mul, neg_neg]
    have c1 : x * a - b * conj y = cdZero := by
      rw [hy, hI, mul_neg, hartRy (x * a), hy2, mul_neg, mul_one, neg_neg,
        sub_self]
    have c2 : conj x * b + a * y = cdZero := by
      rw [hx, neg_mul, hxb, neg_add_self]
    exact congrArg₂ dbl c1 c2

/-!
#### Numeric anchor at the octonion level

The canonical imaginary units of ℂ and ℍ, with all unit facts by
definitional computation, and the iff instantiated at z = i + jℓ ∈ CD 3.
-/

/-- The imaginary unit of ℂ. -/
def imagI : CD 1 := dbl cdZero cdOne

/-- The quaternion unit i, embedded in ℍ. -/
def unitI : CD 2 := dbl imagI cdZero

/-- The new quaternion unit j. -/
def unitJ : CD 2 := dbl cdZero cdOne

theorem conj_imagI : conj imagI = neg imagI := by
  show dbl (conj (cdZero : CD 0)) (neg (cdOne : CD 0))
      = dbl (neg (cdZero : CD 0)) (neg (cdOne : CD 0))
  rw [conj_zero, neg_zero]

theorem imagI_sq : imagI * imagI = neg (cdOne : CD 1) := by
  show dbl ((cdZero : CD 0) * (cdZero : CD 0) - (cdOne : CD 0) * conj (cdOne : CD 0))
      (conj (cdZero : CD 0) * (cdOne : CD 0) + (cdZero : CD 0) * (cdOne : CD 0))
      = dbl (neg (cdOne : CD 0)) (neg (cdZero : CD 0))
  rw [conj_one, mul_one, zero_mul, conj_zero, zero_mul, sub_add, zero_add,
    add_zero, neg_zero]

theorem conj_unitI : conj unitI = neg unitI := by
  show dbl (conj imagI) (neg (cdZero : CD 1))
      = dbl (neg imagI) (neg (cdZero : CD 1))
  rw [conj_imagI]

theorem conj_unitJ : conj unitJ = neg unitJ := by
  show dbl (conj (cdZero : CD 1)) (neg (cdOne : CD 1))
      = dbl (neg (cdZero : CD 1)) (neg (cdOne : CD 1))
  rw [conj_zero, neg_zero]

theorem unitI_sq : unitI * unitI = neg (cdOne : CD 2) := by
  show dbl (imagI * imagI - (cdZero : CD 1) * conj (cdZero : CD 1))
      (conj imagI * (cdZero : CD 1) + imagI * (cdZero : CD 1))
      = dbl (neg (cdOne : CD 1)) (neg (cdZero : CD 1))
  rw [imagI_sq, zero_mul, sub_zero, mul_zero, mul_zero, add_zero, neg_zero]

theorem unitJ_sq : unitJ * unitJ = neg (cdOne : CD 2) := by
  show dbl ((cdZero : CD 1) * (cdZero : CD 1) - (cdOne : CD 1) * conj (cdOne : CD 1))
      (conj (cdZero : CD 1) * (cdOne : CD 1) + (cdZero : CD 1) * (cdOne : CD 1))
      = dbl (neg (cdOne : CD 1)) (neg (cdZero : CD 1))
  rw [conj_one, mul_one, zero_mul, conj_zero, zero_mul, sub_add, zero_add,
    add_zero, neg_zero]

/-- The full alternating art holds at the quaternion level (ℍ is quadratic:
ℂ below it is associative with central trace and norm). -/
theorem art_left_two (x w : CD 2) : x * (x * w) = (x * x) * w :=
  art_left_of_assoc assoc_one trace_central_one norm_central_one x w

theorem art_right_two (w x : CD 2) : (w * x) * x = w * (x * x) :=
  art_right_of_assoc assoc_one trace_central_one norm_central_one w x

/-- Numeric anchor: for z = i + jℓ ∈ CD 3 (octonions), the kernel of L_z is
an exact copy of the kernel of W(a) = (i*a)*j + i*(a*j). -/
theorem ker_Lz_octonion (a b : CD 2) :
    dbl unitI unitJ * dbl a b = (cdZero : CD 3) ↔
    b = (unitI * a) * unitJ ∧ (unitI * a) * unitJ + unitI * (a * unitJ)
      = (cdZero : CD 2) :=
  ker_Lz_iff_ker_W unitI unitJ (art_left_two unitI) (fun w => art_right_two w unitJ)
    conj_unitI conj_unitJ unitI_sq unitJ_sq a b

/-!
#### Chain step (2): diagonal blocks across the doubling

For x, y : CD m and the embedded pair X = (x, 0), Y = (y, 0) : CD (m + 1),
the anti-associator of (X, Y) acting on w = (a₀, a₁) splits into DIAGONAL
blocks: the level-m anti-associator of (x, y) on a₀, and the complementary
block C(u) = y(x̄u) + x̄(yu) = -{L_x, L_y}(u) on a₁ (claims sheet T12,
three-line hand derivation: x·(a₁ℓ₀) = (x̄a₁)ℓ₀ and (a₁ℓ₀)·y = (ya₁)ℓ₀).
Hence ker W at the doubled level is ker W ⊕ ker C, pointwise.
-/

/-- **Chain step (2), block lemma.** The anti-associator
W_T(w) = (X*w)*Y + X*(w*Y) of the embedded pair X = (x,0), Y = (y,0)
decomposes as W_T(a₀, a₁) = (W_A a₀, C a₁): the doubling is DIAGONAL.
No hypotheses -- pure level-m algebra, valid at every floor of the tower,
including the floors where alternativity is dead. -/
theorem W_block {m : ℕ} (x y a₀ a₁ : CD m) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
    = dbl ((x * a₀) * y + x * (a₀ * y))
        (y * (conj x * a₁) + conj x * (y * a₁)) := by
  have hXw : dbl x (cdZero : CD m) * dbl a₀ a₁
      = dbl (x * a₀) (conj x * a₁) := by
    show dbl (x * a₀ - a₁ * conj (cdZero : CD m))
        (conj x * a₁ + a₀ * (cdZero : CD m)) = dbl (x * a₀) (conj x * a₁)
    rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
  have hwY : dbl a₀ a₁ * dbl y (cdZero : CD m)
      = dbl (a₀ * y) (y * a₁) := by
    show dbl (a₀ * y - (cdZero : CD m) * conj a₁)
        (conj a₀ * (cdZero : CD m) + y * a₁) = dbl (a₀ * y) (y * a₁)
    rw [zero_mul, mul_zero, sub_zero, zero_add]
  have h1 : (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      = dbl ((x * a₀) * y) (y * (conj x * a₁)) := by
    rw [hXw]
    show dbl ((x * a₀) * y - (cdZero : CD m) * conj (conj x * a₁))
        (conj (x * a₀) * (cdZero : CD m) + y * (conj x * a₁))
        = dbl ((x * a₀) * y) (y * (conj x * a₁))
    rw [zero_mul, mul_zero, sub_zero, zero_add]
  have h2 : dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = dbl (x * (a₀ * y)) (conj x * (y * a₁)) := by
    rw [hwY]
    show dbl (x * (a₀ * y) - (y * a₁) * conj (cdZero : CD m))
        (conj x * (y * a₁) + (a₀ * y) * (cdZero : CD m))
        = dbl (x * (a₀ * y)) (conj x * (y * a₁))
    rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
  rw [h1, h2]
  rfl

/-- **Chain step (2), kernel split.** The kernel of the doubled
anti-associator is the direct product of the two diagonal blocks:
(a₀, a₁) is killed iff W kills a₀ AND C kills a₁. This is the claims
sheet's ker W_T = ker W_A ⊕ ker C, pointwise. -/
theorem ker_WT_iff {m : ℕ} (x y a₀ a₁ : CD m) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = (cdZero : CD (m + 1)) ↔
    (x * a₀) * y + x * (a₀ * y) = (cdZero : CD m) ∧
    y * (conj x * a₁) + conj x * (y * a₁) = (cdZero : CD m) := by
  rw [W_block]
  constructor
  · intro h
    have h' : dbl ((x * a₀) * y + x * (a₀ * y))
          (y * (conj x * a₁) + conj x * (y * a₁))
        = (dbl (cdZero : CD m) (cdZero : CD m) : CD (m + 1)) := h
    injection h' with hidx h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact congrArg₂ dbl h1 h2

/-- For imaginary x (conj x = -x), the complementary block C is the NEGATIVE
anti-commutator of the left multiplications: C(u) = -{L_x, L_y}(u), the
claims sheet's C = -{L_x, L_y}. -/
theorem C_eq_neg_anticommutator {m : ℕ} (x y u : CD m) (hx : conj x = neg x) :
    y * (conj x * u) + conj x * (y * u)
      = neg (y * (x * u) + x * (y * u)) := by
  rw [hx, neg_mul, neg_mul, mul_neg, neg_add]

/-!
### Seal (2026-10-01)

The fold-law chain through chain steps (1) and (2) is sorry-free:
alternativity of ℍ→ℍ-doubles (R→ℂ→ℍ→𝕆), the kernel isomorphism
ker L_z ≅ ker W with the numeric octonion anchor z = i + jℓ, and the
diagonal block lemma ker W_T = ker W_A ⊕ ker C with C = -{L_x, L_y}.
`#print axioms` below must show only the three standard axioms of Lean's
dependent type theory (propext, Classical.choice, Quot.sound) -- no
`sorryAx`, no hand-added `axiom` decls.
-/

#print axioms assoc_succ_of_comm
#print axioms assoc_one
#print axioms assoc_two
#print axioms art_left_of_assoc
#print axioms art_right_of_assoc
#print axioms art_left_three
#print axioms art_right_three
#print axioms ker_Lz_iff_ker_W
#print axioms ker_Lz_octonion
#print axioms W_block
#print axioms ker_WT_iff
#print axioms C_eq_neg_anticommutator

end Foldlaw