-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf
import Mathlib.Tactic

inductive Ty : Type
| Nat : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow

inductive Exp : Ty → Type
| K {a b : Ty}     :  Exp (a ⇒' b ⇒' a)
| S {a b c : Ty}   :  Exp ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))
| App {a b : Ty}   :  Exp (a ⇒' b) → Exp a → Exp b
| zero             :  Exp Nat
| succ             :  Exp (Nat ⇒' Nat)
| recN {a : Ty}    :  Exp (a ⇒' (Nat ⇒' a ⇒' a) ⇒' Nat ⇒' a)
open Exp
infixl : 100 " ⬝ " => App


inductive convr : Π {α : Ty}, (Exp α) → (Exp α) → Prop
| refl {α : Ty}{e : Exp α}
        : convr (e) (e)
| sym   {α : Ty}{e e' : Exp α}
        : convr (e) (e') → convr (e') (e)
| trans {α : Ty}{e e' e'' : Exp α}
        : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
| K     {α β : Ty}{x : Exp α} {y : Exp β}
        : convr (K ⬝ x ⬝ y) (x)
| S     {α β γ: Ty}{x : Exp (γ ⇒' β ⇒' α)} {y : Exp (γ ⇒' β)} {z : Exp γ}
        : convr (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app   {α β : Ty} {a b : Exp (β ⇒' α)} {c d : Exp β}
        : convr (a) (b) → convr (c) (d) → convr (a ⬝ c) (b ⬝ d)
| recN_zero {α : Ty} {e : Exp α} {f : Exp (Nat ⇒' α ⇒' α)}
        : convr (recN ⬝ e ⬝ f ⬝ zero) (e)
| recN_succ {α : Ty} {n : Exp Nat} {e : Exp α} {f : Exp (Nat ⇒' α ⇒' α)}
        : convr (recN ⬝ e ⬝ f ⬝ (succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))




def Ty_inter : Ty → Type
| Ty.Nat => ℕ

| arrow a b => Exp (a ⇒' b) × (Ty_inter a → Ty_inter b)


def appsem {a b : Ty} (t : Ty_inter (a ⇒' b)) (e' : Ty_inter a) : Ty_inter b := (t.snd e')

def reify (a : Ty) (e : Ty_inter a) : Exp a :=
/-
| Ty.Nat, (0 : ℕ) => zero
| Ty.Nat, n+1     => succ ⬝ (reify Ty.Nat n)

| Ty.arrow a b, (c, f) => c
-/
by
  cases a
  case Nat =>
    induction e
    case zero           => exact zero
    case succ n reify_n => exact (succ ⬝ reify_n)
  case arrow a b        => exact e.fst


def Exp_inter (a : Ty) : (e : Exp a) → Ty_inter a
| @K a b => (K,
            (λ p ↦ (K ⬝ (reify a p),
            (λ q ↦ p))))
| @S a b c => (S,
              (λ x ↦ (S ⬝ (reify (a⇒'b⇒'c) x),
              (λ y ↦ (S ⬝ (reify (a⇒'b⇒'c) x) ⬝ (reify (a⇒'b) y),
              (λ z ↦ appsem (appsem x z) (appsem y z)))))))
| @App a b f e  => appsem (Exp_inter (a ⇒' b) f) (Exp_inter a e)
| zero          => (0 : ℕ)
| succ          => (succ,
                   (λ n : ℕ ↦ n+1) )
| @recN a       => (recN,
                   (λ p ↦ (recN ⬝ (reify a p),
                   (λ q ↦ (recN ⬝ (reify a p) ⬝ (reify (Nat⇒'a⇒'a) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))


def nbe (a : Ty) (e : Exp a) : (Exp a) := reify a (Exp_inter a e)


-- e ~ e'  implies [[e]]a = [[e']]a
lemma convr_lemma1 {a : Ty} {e e' : Exp a} : convr e e' → ((Exp_inter a e) = (Exp_inter a e')) :=
by
  intro h
  induction h
  any_goals aesop
  case app α β a b c d a_r_b c_r_d ab_ih cd_ih =>
    unfold Exp_inter
    rw [ab_ih, cd_ih]

-- e ~ e'  implies nbe a e = nbe a e'
lemma soundness {a : Ty} {e e' : Exp a} : convr e e' → nbe a e = nbe a e' :=
by
  unfold nbe
  intro h1
  have h2 : Exp_inter a e = Exp_inter a e' := convr_lemma1 h1
  rw [h2]


-- Tait-reducibility relation
def R : (a : Ty) → (e : Exp a) → Prop
| Ty.Nat, e       => convr e (nbe Ty.Nat e)

| Ty.arrow α β, e => convr e (nbe (α ⇒' β) e)  ∧  ∀ e', R α e' → R β (App e e')

-- R a e  implies  e ~ nbe a e
lemma R_convr_nbe (h : R a e)  : convr e (nbe a e) :=
  by
  cases a
  all_goals (unfold R at h); aesop

-- e ~ e' implies  R α e ↔ R α e'
lemma convr_R_iff : ∀ e e', convr e e' → (R α e ↔ R α e') :=
  by
  induction α
  · unfold R
    intro a b a_r_b
    apply Iff.intro
    · intro a_r_nbe
      have eq : nbe Ty.Nat a = nbe Ty.Nat b := soundness a_r_b
      (rewrite [← eq]); clear eq
      apply convr.trans (a_r_b).sym
      exact a_r_nbe
    -- Symmetric case
    · intro b_r_nbe
      have eq : nbe Ty.Nat a = nbe Ty.Nat b := soundness a_r_b
      (rewrite [eq]); clear eq
      exact convr.trans a_r_b b_r_nbe

  · rename_i α β αIH βIH
    intros f1 f2 f1_r_f2
    apply Iff.intro
    · intro R_f1
      apply And.intro
      · apply convr.trans (f1_r_f2).sym
        have eq : nbe (α ⇒' β) f1 = nbe (α ⇒' β) f2 := soundness f1_r_f2
        rewrite [← eq]; clear eq
        exact R_convr_nbe R_f1
      · intro e' Re'
        specialize βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app convr.refl)
        apply βIH.mp
        rcases R_f1 with ⟨_, h0⟩
        exact h0 e' Re'
    -- Symmetric case
    · intro R_f2
      apply And.intro
      · apply (f1_r_f2).trans
        have eq : nbe (α ⇒' β) f1 = nbe (α ⇒' β) f2 := soundness f1_r_f2
        rewrite [eq]; clear eq
        exact R_convr_nbe R_f2
      · intro e' Re'
        specialize βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app convr.refl)
        apply βIH.mpr
        rcases R_f2 with ⟨_, h0⟩
        exact h0 e' Re'


def numeral : ℕ → Exp Ty.Nat
| 0 => zero

| n+1 => succ ⬝ (numeral n)


/-
lemma  ∃ n, reify Ty.Nat k = (numeral n)
(induction on k)
k = 0  implies  reify Ty.Nat 0 = zero

k = k'+1
reify Ty.Nat (k'+1)
=
succ ⬝ (reify Ty.Nat k')
=                         (IH)
succ ⬝ (numeral n)
=
numeral (n+1)
QED
-/
lemma reify_Nat : ∃ n, reify Ty.Nat k = (numeral n) :=
  by
  induction k
  case zero =>
    use 0; rfl

  case succ k' IH =>
    rcases IH with ⟨n, eq⟩
    use n+1
    simp [reify]
    unfold numeral
    exact congrArg succ.App eq

lemma nbe_Nat : ∃ n, nbe Ty.Nat e = numeral n := reify_Nat

/-
lemma R Ty.Nat (numeral n)
(induction n)
n = 0  implies R Ty.Nat zero = zero ~ zero

n = n'+1
R Ty.Nat (numeral (n'+1))
=                                                                [R]
(numeral (n'+1)) ~ nbe Ty.Nat (numeral (n'+1))
=                                                                [numeral]
(succ ⬝ numeral n') ~ nbe Ty.Nat (succ ⬝ numeral n')
=                                                                [nbe, Exp_inter, appsem]
(succ ⬝ numeral n') ~ reify Ty.Nat ([[numeral n']] Nat + 1)
=                                                                [reify]
(succ ⬝ numeral n') ~ succ ⬝ (reify Ty.Nat [[numeral n']] Nat)
=                                                                [nbe]
(succ ⬝ numeral n') ~ succ ⬝ (nbe Ty.Nat (numeral n'))
=                                                                [convr.app convr.refl]
numeral n' ~ nbe Ty.Nat (numeral n')
=                                                                [IH]
QED
-/
lemma R_numeral : R Ty.Nat (numeral n) :=
  by
  unfold R
  induction n
  case zero => exact convr.refl

  case succ n' IH =>
    unfold numeral
    apply (convr.refl).app
    exact IH

-- for all e, R a e
lemma all_R {e : Exp a} : R a e :=
  by
  induction e
  all_goals clear a
  case K a b =>
    apply And.intro
    · exact convr.refl
    · intro e' Re'
      apply And.intro
      · unfold nbe
        (generalize eq : (Exp_inter (b ⇒' a) (K ⬝ e')) = cf); rcases cf with ⟨c,f⟩
        simp [reify]
        cases eq
        apply convr.app convr.refl
        exact R_convr_nbe Re'
      · intro e'' Re''
        apply (convr_R_iff (K ⬝ e' ⬝ e'') e' convr.K).mpr
        exact Re'

  case S a b c =>
    apply And.intro
    · exact convr.refl
    · intro x Rx
      apply And.intro
      · unfold nbe
        (generalize eq : (Exp_inter ((a ⇒' b) ⇒' a ⇒' c) (S ⬝ x)) = cf); rcases cf with ⟨c,f⟩
        simp [reify]
        cases eq
        apply convr.app convr.refl
        exact R_convr_nbe Rx
      · intro y Ry
        apply And.intro
        · unfold nbe
          (generalize eq : (Exp_inter (a ⇒' c) (S ⬝ x ⬝ y)) = cf); rcases cf with ⟨c,f⟩
          simp [reify]
          cases eq
          replace Rx := R_convr_nbe Rx; replace Ry := R_convr_nbe Ry
          have Sx_r_S_nbex : convr (S ⬝ x) (S ⬝ (nbe (a ⇒' b ⇒' c) x)) := (convr.refl).app Rx
          exact Sx_r_S_nbex.app Ry
        · intro z Rz
          apply (convr_R_iff (S ⬝ x ⬝ y ⬝ z) _ convr.S).mpr
          rcases Rx with ⟨_, Rxz⟩; specialize Rxz z Rz
          rcases Ry with ⟨_, Ryz⟩; specialize Ryz z Rz
          rcases Rxz with ⟨_, Rxzyz⟩; specialize Rxzyz (y ⬝ z) Ryz
          exact Rxzyz

  case App α β f x Rf Rx =>
    rcases Rf with ⟨_, h0⟩
    exact h0 x Rx

  case zero =>
    exact convr.refl

  case succ =>
    apply And.intro
    · exact convr.refl
    · intro x Rx
      unfold R nbe Exp_inter
      (generalize eq : (Exp_inter (Ty.Nat ⇒' Ty.Nat) succ) = cf); rcases cf with ⟨c,f⟩
      simp [appsem]
      cases eq; simp
      simp [reify]
      exact (convr.refl).app Rx

  case recN α =>
    apply And.intro
    · exact convr.refl
    · intro e' Re'
      apply And.intro
      · unfold nbe
        (generalize eq : (Exp_inter ((Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) (recN ⬝ e')) = cf); rcases cf with ⟨c,f⟩
        simp [reify]
        cases eq
        apply convr.app convr.refl
        exact R_convr_nbe Re'
      · intro e'' Re''
        apply And.intro
        · unfold nbe
          (generalize eq : (Exp_inter (Ty.Nat ⇒' α) (recN ⬝ e' ⬝ e'')) = cf); rcases cf with ⟨c,f⟩
          simp [reify]
          cases eq
          replace Re' := R_convr_nbe Re'; replace Re'' := R_convr_nbe Re''
          have h0 : convr (recN ⬝ e') (recN ⬝ nbe α e') := (convr.refl).app Re'
          exact h0.app Re''
        · intro n Rn
          have convr_n := Rn
          unfold R at convr_n
          apply (convr_R_iff (recN ⬝ e' ⬝ e'' ⬝ n) (recN ⬝ e' ⬝ e'' ⬝ (nbe Ty.Nat n)) (convr.refl.app Rn)).mpr
          have : ∃ n₁, nbe Ty.Nat n = numeral n₁ := by exact nbe_Nat
          rcases this with ⟨n₁, eq⟩; rewrite [eq] at convr_n ⊢; clear eq
          (have R_numeral : R Ty.Nat (numeral n₁) := by exact (convr_R_iff n (numeral n₁) convr_n).mp Rn); clear Rn convr_n n
          induction n₁
          · unfold numeral
            exact (convr_R_iff (recN ⬝ e' ⬝ e'' ⬝ zero) e' convr.recN_zero).mpr Re'
          · rename_i n' IH
            unfold numeral at R_numeral ⊢
            apply (convr_R_iff (recN ⬝ e' ⬝ e'' ⬝ (succ ⬝ numeral n')) (e'' ⬝ (numeral n') ⬝ (recN ⬝ e' ⬝ e'' ⬝ (numeral n'))) convr.recN_succ).mpr
            have : R Ty.Nat (numeral n') := by exact _root_.R_numeral
            specialize IH this
            rcases Re'' with ⟨_, h0⟩
            specialize h0 (numeral n') this
            rcases h0 with ⟨_, h0⟩
            exact h0 (recN ⬝ e' ⬝ e'' ⬝ numeral n') IH


-- e ~ nbe a e
lemma convr_nbe {e : Exp a} : convr e (nbe a e) := R_convr_nbe all_R

-- nbe a e = nbe a e' implies e ~ e'
lemma completeness : nbe a e = nbe a e' → convr e e' :=
  by
  intro eq
  apply (convr_nbe).trans
  rewrite [eq]; clear eq
  exact convr_nbe.sym

-- e ~ e' ↔ nbe a e = nbe a e'
lemma correctness {e e' : Exp a} : convr e e' ↔ nbe a e = nbe a e' := ⟨soundness, completeness⟩
