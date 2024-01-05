open Classical

variable (α β : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hpq: ∀ x, p x ∧ q x =>
      And.intro
        (fun x: α => (hpq x).left)
        (fun x: α => (hpq x).right))
    (fun hpq: (∀ x, p x) ∧ (∀ x, q x) =>
      (fun x: α => And.intro (hpq.left x) (hpq.right x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun hpq: ∀ x, p x → q x =>
    (fun hp: ∀ x, p x =>
      (fun x: α =>
        hpq x (hp x))))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun hpq: (∀ x, p x) ∨ (∀ x, q x) =>
    (fun x: α =>
      Or.elim hpq
        (fun hp: ∀ x, p x => Or.intro_left (q x) (hp x))
        (fun hq: ∀ x, q x => Or.intro_right (p x) (hq x))))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  (fun x: α => Iff.intro
    (fun hpr: ∀ _: α, r => hpr x)
    (fun hr: r => (fun _: α => hr)))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun hpr: ∀ x, p x ∨ r =>
      Or.elim (em r)
        (fun hr: r => Or.intro_right (∀ x, p x) hr)
        (fun hnr: ¬r =>
          have hp: (∀ x, p x) :=
            (fun x => Or.elim (hpr x)
              (fun hp: p x => hp)
              (fun hr: r => absurd hr hnr));
          Or.intro_left r hp))
    (fun hpr: (∀ x, p x) ∨ r =>
      (fun x: α => Or.elim hpr
        (fun hp: ∀ x, p x => Or.intro_left r (hp x))
        (fun r => Or.intro_right (p x) r)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun hrp: ∀ x, r → p x =>
      (fun r =>
        (fun x: α => hrp x r)))
    (fun hrp: r → ∀ x, p x =>
      (fun x: α =>
        fun r =>
          hrp r x))

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hpp: shaves barber barber ↔ ¬shaves barber barber := (h barber);
  -- The rest copy/pasted from the last exercise in propositional_logic.lean
  have hpnp: shaves barber barber → ¬shaves barber barber := hpp.mp;
  have hnp: ¬shaves barber barber := (fun hp: shaves barber barber => absurd hp (hpnp hp));
  have hnpp: ¬shaves barber barber → shaves barber barber := hpp.mpr;
  have hp: shaves barber barber := hnpp hnp;
  hnp hp

def even (n : Nat) : Prop := n % 2 = 0

def prime (n : Nat) : Prop := ∀ m : Nat, (n % m = 0) → (m = n) ∨ (m = 1)

def infinitely_many_primes : Prop := ∀ m : Nat, ∃ p : Nat, prime p ∧ p > m

def fermat_prime (n : Nat) : Prop := prime n ∧ ∃ m : Nat, n = 2^(2^m) + 1

def infinitely_many_Fermat_primes : Prop := ∀ m : Nat, ∃ fp : Nat, fermat_prime fp ∧ fp > m

def goldbach_conjecture : Prop := ∀ n : Nat, even n ∧ n > 2 → ∃ p1 : Nat, ∃ p2 : Nat, prime p1 ∧ prime p2 ∧ (p1 + p2 = n)

def goldbach's_weak_conjecture : Prop := ∀ n : Nat, (¬even n) ∧ n > 5 → ∃ p1 : Nat, ∃ p2 : Nat, ∃ p3 : Nat, prime p1 ∧ prime p2 ∧ prime p3 ∧ (p1 + p2 + p3 = n)

def fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 → ¬(∃ a: Nat, ∃ b: Nat, ∃ c: Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ (a^n + b^n = c^n))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun ⟨ _, hr ⟩ => hr

example (a : α) : r → (∃ _ : α, r) :=
 (fun hr: r => Exists.intro a hr)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨ w, ⟨ hpw, hr ⟩ ⟩ => And.intro (Exists.intro w hpw) hr)
    (fun ⟨ ⟨ w, pw ⟩, hr ⟩ => Exists.intro w (And.intro pw hr))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨ w, hpqw ⟩ =>
      Or.elim hpqw
        (fun hp: p w => Or.intro_left (∃ x, q x) (Exists.intro w hp))
        (fun hq: q w => Or.intro_right (∃ x, p x) (Exists.intro w hq)))
    (fun hpq =>
      Or.elim hpq
        (fun ⟨ w, pw ⟩ => Exists.intro w (Or.intro_left (q w) pw))
        (fun ⟨ w, pq ⟩ => Exists.intro w (Or.intro_right (p w) pq)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hp: (∀ x, p x) =>
      (fun ⟨ w, hnpw ⟩ => hnpw (hp w)))
    (fun hnnp: ¬(∃ x, ¬ p x) =>
      (fun x: α =>
        byContradiction
          (fun hnp: ¬ p x => hnnp (Exists.intro x hnp))))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨ w, pw ⟩ =>
      (fun hnp: (∀ x, ¬ p x) => (hnp w) pw) )
    (fun hnp: ¬(∀ x, ¬ p x) =>
      byContradiction
        (fun hnp2: ¬(∃ x, p x) =>
          hnp (fun x: α => (fun hp: p x => hnp2 (Exists.intro x hp)))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hnp: ¬ ∃ x, p x =>
      (fun x: α =>
        (fun hp: p x => hnp (Exists.intro x hp))))
    (fun hnp: (∀ x, ¬ p x) =>
      (fun ⟨ w, pw ⟩ => (hnp w) pw))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hnp: ¬ ∀ x, p x =>
      byContradiction
        (fun hnp2: ¬ ∃ x, ¬ p x =>
          hnp (fun x: α =>
            byContradiction
              (fun hnp3: ¬ p x =>
                have hp: ∃ x, ¬ p x := (Exists.intro x hnp3);
                hnp2 hp))))
    (fun ⟨ w, hnpw ⟩ =>
      (fun hp : ∀ x, p x => hnpw (hp w)))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun hpr: ∀ x, p x → r =>
      (fun ⟨ w, pw ⟩ => hpr w pw))
    (fun hpr: (∃ x, p x) → r =>
      (fun x: α =>
        (fun hp: p x => hpr (Exists.intro x hp))))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨ w, pwr ⟩ =>
      (fun hp: (∀ x, p x) => pwr (hp w)))
    (fun hpr: (∀ x, p x) → r =>
      Or.elim (em (∀ x, p x))
        (fun hp: ∀ x, p x => Exists.intro a (fun _: p a => hpr hp))
        (fun hnp: ¬∀ x, p x => byContradiction
          (fun hnpr: ¬∃ x, p x → r =>
            have hap: ∀ x, p x :=
              (fun x => byContradiction
                (fun hnp: ¬p x =>
                  have hpr: ∃ x, p x → r := Exists.intro x (fun hp: p x => absurd hp hnp);
                  hnpr hpr));
            hnp hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨ w, hrpw ⟩ =>
      (fun hr: r => Exists.intro w (hrpw hr)))
    (fun hrp: r → ∃ x, p x =>
      Or.elim (em r)
        (fun hr: r =>
          have ⟨ w, pw ⟩ := hrp hr;
          Exists.intro w (fun _: r => pw))
        (fun hnr: ¬ r => Exists.intro a (fun hr: r => absurd hr hnr)))
