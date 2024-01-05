open Classical

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hpq: p ∧ q => ⟨ hpq.right, hpq.left ⟩)
    (fun hqp: q ∧ p => ⟨ hqp.right, hqp.left ⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq: p ∨ q =>
      Or.elim hpq
              (fun hp: p => Or.intro_right q hp)
              (fun hq: q => Or.intro_left p hq))
    (fun hqp: q ∨ p =>
      Or.elim hqp
              (fun hq: q => Or.intro_right p hq)
              (fun hp: p => Or.intro_left q hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun hpqr: (p ∧ q) ∧ r =>
      ⟨ hpqr.left.left, hpqr.left.right, hpqr.right ⟩)
    (fun hpqr: p ∧ (q ∧ r) =>
      ⟨ ⟨ hpqr.left, hpqr.right.left ⟩, hpqr.right.right ⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr: (p ∨ q) ∨ r =>
      Or.elim hpqr
        (fun hpq: p ∨ q => Or.elim hpq
          (fun hp: p => Or.intro_left (q ∨ r) hp)
          (fun hq: q => Or.intro_right p (Or.intro_left r hq)))
        (fun hr: r => Or.intro_right p (Or.intro_right q hr)))
    (fun hpqr: p ∨ (q ∨ r) =>
      Or.elim hpqr
        (fun hp: p => Or.intro_left r (Or.intro_left q hp))
        (fun hqr: q ∨ r => Or.elim hqr
          (fun hq: q => Or.intro_left r (Or.intro_right p hq))
          (fun hr: r => Or.intro_right (p ∨ q) hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hpqr: p ∧ (q ∨ r) =>
      Or.elim hpqr.right
        (fun hq: q => Or.intro_left (p ∧ r) ⟨ hpqr.left, hq ⟩)
        (fun hr: r => Or.intro_right (p ∧ q) ⟨ hpqr.left, hr ⟩))
    (fun hpqpr: (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqpr
        (fun hpq: p ∧ q => ⟨ hpq.left , Or.intro_left r hpq.right ⟩)
        (fun hpr: p ∧ r => ⟨ hpr.left, Or.intro_right q hpr.right ⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr: p ∨ (q ∧ r) =>
      have hpq: p ∨ q :=
        Or.elim hpqr
          (fun hp: p => Or.intro_left q hp)
          (fun hqr: q ∧ r => Or.intro_right p hqr.left);
      have hpr: p ∨ r :=
        Or.elim hpqr
          (fun hp: p => Or.intro_left r hp)
          (fun hqr: q ∧ r => Or.intro_right p hqr.right);
      ⟨ hpq, hpr ⟩)
    (fun hpqpr: (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hpqpr.left
        (fun hp: p => Or.intro_left (q ∧ r) hp)
        (fun hq: q =>
          Or.elim hpqpr.right
            (fun hp: p => Or.intro_left (q ∧ r) hp)
            (fun hr: r => Or.intro_right p ⟨ hq, hr ⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr: p → (q → r) =>
      (fun hpq: p ∧ q =>
        hpqr hpq.left hpq.right))
    (fun hpqr: p ∧ q → r =>
      (fun hp: p =>
        (fun hq: q =>
          hpqr ⟨ hp, hq ⟩)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr: (p ∨ q) → r =>
      And.intro
        (fun hp: p => hpqr (Or.intro_left q hp))
        (fun hq: q => hpqr (Or.intro_right p hq)))
    (fun hprqr: (p → r) ∧ (q → r) =>
      (fun hpqr: (p ∨ q) =>
        Or.elim hpqr
          (fun hp: p => hprqr.left hp)
          (fun hq: q => hprqr.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpq: ¬(p ∨ q) =>
      And.intro
        (fun hp: p => hnpq (Or.intro_left q hp))
        (fun hq: q => hnpq (Or.intro_right p hq)))
    (fun hnpq: ¬p ∧ ¬q =>
      fun hpq: p ∨ q =>
        Or.elim hpq
          (fun hp: p => hnpq.left hp)
          (fun hq: q => hnpq.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun hpq: ¬p ∨ ¬q =>
    Or.elim hpq
      (fun hp: ¬p => (fun hpq: p ∧ q => hp hpq.left))
      (fun hq: ¬q => (fun hpq: p ∧ q => hq hpq.right)))

example : ¬(p ∧ ¬p) :=
  (fun hpp: p ∧ ¬p => hpp.right hpp.left)

example : p ∧ ¬q → ¬(p → q) :=
  (fun hpq: p ∧ ¬q =>
    (fun hnpq: p → q =>
      have hq : q := hnpq hpq.left;
      hpq.right hq))

example : ¬p → (p → q) :=
  (fun hnp: ¬p =>
    (fun hp: p => absurd hp hnp))

example : (¬p ∨ q) → (p → q) :=
  (fun hnpq: ¬p ∨ q =>
    (fun hp: p =>
      Or.elim hnpq
        (fun hnp: ¬p => absurd hp hnp)
        (fun hq: q => hq)))

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf: p ∨ False =>
      Or.elim hpf
        (fun hp: p => hp)
        (fun f: False => False.elim f))
    (fun hp: p => Or.intro_left False hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun hpf: p ∧ False => hpf.right)
    (fun hf: False => False.elim hf)

example : (p → q) → (¬q → ¬p) :=
  (fun hpq: p → q =>
    (fun hnq: ¬q =>
      (fun hp: p =>
        have hq: q := hpq hp;
        hnq hq)))

---- Classical reasoning ----

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun hpqr: p → q ∨ r =>
    Or.elim (em p)
      (fun hp: p => Or.elim (hpqr hp)
        (fun hq: q => Or.intro_left (p → r) (fun _ => hq))
        (fun hr: r => Or.intro_right (p → q) (fun _ => hr)))
      (fun hnp: ¬p => Or.intro_left (p → r) (fun hp: p => absurd hp hnp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun hnpq: ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp: p =>
        Or.elim (em q)
          (fun hq: q =>
            have hpq: p ∧ q := And.intro hp hq;
            absurd hpq hnpq)
          (fun hnq: ¬q => Or.intro_right (¬p) hnq))
      (fun hnp: ¬p => Or.intro_left (¬q) hnp))

example : ¬(p → q) → p ∧ ¬q :=
  (fun hnpq: ¬(p → q) =>
    Or.elim (em q)
      (fun hq: q => False.elim (hnpq (fun _ => hq)))
      (fun hnq: ¬q =>
        Or.elim (em p)
          (fun hp: p => And.intro hp hnq)
          (fun hnp: ¬p => False.elim (hnpq (fun hp: p => absurd hp hnp)))))

example : (p → q) → (¬p ∨ q) :=
  (fun hpq: p → q =>
    Or.elim (em p)
      (fun hp: p => Or.intro_right (¬p) (hpq hp))
      (fun hnp: ¬p => Or.intro_left q hnp))

example : (¬q → ¬p) → (p → q) :=
  (fun hnqnp: ¬q → ¬p =>
    (fun hp: p =>
      Or.elim (em q)
        (fun hq: q => hq)
        (fun hnq: ¬q => absurd hp (hnqnp hnq))))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  (fun hpqp: (p → q) → p =>
    Or.elim (em p)
      (fun hp: p => hp)
      (fun hnp: ¬p => hpqp (fun hp: p => absurd hp hnp)))

example : ¬(p ↔ ¬p) :=
  (fun hpp: p ↔ ¬p =>
    have hpnp: p → ¬p := hpp.mp;
    have hnp: ¬p := (fun hp: p => absurd hp (hpnp hp));
    have hnpp: ¬p → p := hpp.mpr;
    have hp: p := hnpp hnp;
    hnp hp)
