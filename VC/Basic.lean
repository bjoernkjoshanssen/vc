/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib
-- import Mathlib.NumberTheory.Padics.PadicVal
-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Algebra.Order.Floor
-- import Mathlib.Analysis.SpecialFunctions.Log.Base


/-!

# Definition 10, Lemma 11, and Lemma 12 from the paper
# "VC-dimensions of nondeterministic finite automata for words of equal length".

-/
set_option tactic.hygienic false


def t (n : ℕ) : ℕ := padicValNat 2 n

def a (n : ℕ) : ℕ := by
    induction n with
    | zero => exact 0
    | succ n_1 n_ih => exact n_ih + 1 + t n_1.succ

-- Instead of using Mathlib.Data.Nat.Digits we use:
def F : Bool → ℕ := fun b ↦ ite (b=true) 1 0

-- w = binaryHammingWeight (Lemma 11 of VC paper)
def w : ℕ → ℕ := fun n ↦  List.sum (List.map F (Nat.bits n))

theorem bits_bool (b : Bool) (n : ℕ) (h : n ≠ 0) : Nat.bits (Nat.bit b n) = b :: Nat.bits n
:= Nat.bits_append_bit n b (by {intro H;exfalso;exact h H})


theorem bits_odd {n : ℕ} : Nat.bits (2*n+1) = true :: Nat.bits n := by {
  let G := Nat.bits_append_bit n true (by {intro;rfl}); rw [← G]; congr
}

theorem bits_even {n : ℕ} (h : n ≠ 0) : Nat.bits (2*n) = false :: Nat.bits n := by {
  let G := bits_bool false n h; rw [← G]; unfold Nat.bit; simp
}

theorem w_2 (n : ℕ) : w (2*n) = w n := by
    unfold w
    by_cases h:(n=0)
    · subst h; simp
    · rw [bits_even h]
      simp [F]

theorem t_odd (n : ℕ) : t (2*n+1) = 0:= by
  apply padicValNat.eq_zero_of_not_dvd
  omega

theorem t_odd' (n : ℕ) : t (n+n+1) = 0:= by {rw [← t_odd n]; congr; ring}

theorem t_2 (n : ℕ) (h : 0 < n) : t (2*n) = t n + 1:= by
    unfold t
    rw [padicValNat.mul]
    · ring_nf
      simp
    · linarith
    · linarith

theorem w_odd (n : ℕ) : w (2*n+1) = w n + 1 := by
    unfold w
    rw [bits_odd]
    simp only [List.map_cons, List.sum_cons]
    rw [add_comm]; unfold F; simp

theorem w_odd' (n : ℕ) : w (n+n + 1) = w n + 1:= by {rw [← w_odd n]; congr; ring}

theorem lemma11_01 (n : ℕ) :
  t n.succ + w (n + 1) = w n + 1 := by {
    induction' n using Nat.strong_induction_on with n ih -- https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
    by_cases he: (Even n)
    rcases he with ⟨k,hk⟩
    by_cases hn: (n=0)
    subst hn; simp; unfold t; simp; unfold w; simp; rfl

    have h₁: 0 < k := Nat.pos_of_ne_zero (by {
      intro hc; subst hc; simp at hk; exact hn hk
    })
    have h₃: k < n := calc
      k < k + k := Nat.add_lt_add_left h₁ k
      _ = n := hk.symm
    let G := ih k h₃
    have : w (2*k) = w k := w_2 _
    have : w n = w k := by {rw [← this,two_mul,hk];}
    rw [this, ← G]
    subst hk
    by_cases hk:(k=1)
    subst hk

    rw [←two_mul,w_2,w_odd,Nat.succ_eq_add_one,t_odd,Nat.succ_eq_add_one,← two_mul,t_2,t_odd 0]
    ring; linarith
    have : 1 < k := by {by_contra hc; cases (Nat.not_lt.mp hc); contrapose hk; simp; cases a; contrapose h₁; simp}
    apply Nat.succ_injective
    · conv =>
        right
        rw [Nat.succ_eq_add_one,add_assoc]
      have hw: w (k + k + 1) = w k + 1 := w_odd' _
      have : t (k+k).succ = 0 := t_odd' _
      rw [hw,← G,this]
      simp
      · linarith

    have : Odd n := Nat.not_even_iff_odd.mp he
    rcases this with ⟨k,hk⟩
    subst hk
    have : w (2*(k+1)) = w (k+1) := w_2 _
    have : w (2*k+1+1) = w (k+1) := by {
      rw [← this];
      exact congr_arg w (by linarith)
    }
    rw [this]
    have h₀: w (2*k+1) = w k + 1 := w_odd _
    rw [h₀]
    by_cases hk:(k=0)
    · subst hk; simp
      simp_all [t, w]
    have : t ((2*(k+1))) = t (k+1) + 1 := t_2 _ (by linarith)
    have : t ((2*k+1).succ) = t (k+1) + 1 := by {rw [←this];congr;}
    rw [this,add_comm,← add_assoc]
    simp only [Nat.add_right_cancel_iff]
    rw [add_comm]
    exact ih k (by linarith)
  }

theorem lemma11_1 (n : ℕ) :
  t n.succ + w (2 * (n + 1)) = w (2 * n) + 1 := by {
    rw [w_2,w_2]
    exact lemma11_01 _
  }

theorem lemma11 (m : ℕ) : a m + w (2*m) = 2*m := by {
  induction m with
  | zero => simp;constructor <;> rfl
  | succ n n_ih =>
  unfold a
  simp only [Nat.succ_eq_add_one]
  exact Nat.add_right_cancel (calc
    _ = a n + 1 + t n.succ + w (2*(n.succ))+ w (2*n) := rfl
    _ = a n + w (2*n) + 1 + t n.succ + w (2*n.succ)  := by ring
    _ = (2*n)         + 1 + t n.succ + w (2*n.succ)  := by rw [n_ih]
    _ = (2*n) + 1 + (t n.succ + w (2*n.succ))        := by ring
    _ = (2*n) + 1 + (w (2*n) + 1)                    := by rw [lemma11_1]
    _ = _                                            := by linarith)
}

theorem boolBound (b : Bool) : F b ≤ 1 := by
    unfold F
    cases b
    · simp
    · exact le_refl 1

theorem length_map_sum (l : List Bool) :  List.sum (List.map F (l)) ≤ List.length (l) := by {
  induction l
  · simp
  rw [List.length_cons,List.map_cons,List.sum_cons]; calc
  F head + List.sum (List.map F tail) ≤ 1 + List.sum (List.map F tail) :=
    Nat.add_le_add_right (boolBound head) _
  _                                   ≤ 1 + List.length tail           :=
    Nat.add_le_add_left tail_ih _
  _                                   = Nat.succ (List.length tail)    := by linarith
}

theorem wehave (n : ℕ) : n.succ ≤ 2 ^ (Nat.clog 2 n.succ) := Nat.le_pow_clog (by linarith) _

theorem rescue_lemma_12 (n : ℕ) (h : n ≠ 0) : (2*n).succ < 2 ^ (Nat.clog 2 (2*n).succ) := by {
  cases (Nat.lt_or_eq_of_le (wehave _))
  · assumption
  exfalso
  have : ∃ m, n = Nat.succ m := Nat.exists_eq_succ_of_ne_zero h
  rcases this with ⟨m,hm⟩
  have : Nat.clog 2 2 ≤ Nat.clog 2 (Nat.succ (2 * n)) := Nat.clog_mono_right 2 (by linarith)
  have : ∃ k, Nat.clog 2 (Nat.succ (2 * n)) = Nat.succ k :=
    Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp this)
  rcases this with ⟨k,hk⟩
  have : 2 ^ Nat.clog 2 (Nat.succ (2 * n)) = 2 * 2^ (Nat.clog 2 (Nat.succ (2 * n)) - 1) := by
    rw [hk,pow_succ]
    ring_nf
    congr
  omega
}

theorem mentioned_in_lemma_12 {n s : ℕ} (h : n < 2 ^ s) : w n ≤ s := calc
_ ≤ List.length (Nat.bits n) := by {unfold w; exact length_map_sum _}
_ ≤ _                        := by {rw [Nat.size_eq_bits_len,Nat.size_le,];assumption}

theorem andhence (n : ℕ) (h : n ≠ 0) : w (2*n) < Nat.clog 2 (2*n).succ := calc
  w (2*n) < w (2*n + 1) := by {rw [w_odd,w_2];simp;}
  _       ≤ _           := mentioned_in_lemma_12 (rescue_lemma_12 _ h)

theorem almost_lemma12 (n : ℕ) (h : n ≠ 0) : a n + Nat.clog 2 (2*n).succ > 2*n := calc
  _ > a n + w (2*n) := Nat.add_lt_add_left (andhence n h) _
  _ = 2 * n := lemma11 n

theorem lemma12 (n : ℕ) : a n + Nat.clog 2 (n).succ ≥ 2*n := by {
  by_cases h:(n=0)
  · subst h;simp
  have : 2 ≤ (2*n).succ := le_of_lt (calc
         2 = 2*1        := by ring
         _ ≤ 2*n        := Nat.mul_le_mul_left 2 (Nat.one_le_iff_ne_zero.mpr h)
         _ < (2*n).succ := Nat.lt_add_one (2 * n))
  have hkey: Nat.clog 2 (Nat.succ n) + 1 ≥ Nat.clog 2 (Nat.succ (2 * n)) := by {
    rw [Nat.clog_of_two_le one_lt_two this] -- strange but wonderful!
    simp
  }
  have : a n + Nat.clog 2 (Nat.succ n) + 1   ≥ (2 * n).succ := calc
     _ ≥ a n + Nat.clog 2 (Nat.succ (2 * n)) := Nat.add_le_add_left hkey _
     _ ≥ _                                   := almost_lemma12 n h
  exact Nat.le_of_lt_succ this
}
