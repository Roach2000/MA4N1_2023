/-
GENERAL COMMENTS:
please change the names for definitions and theorems if you have a good idea
please add nice comments explaining our working if you have a good idea
-/


import Mathlib.Data.ZMod.Basic --includes definition of modular equality
-- import Mathlib.GroupTheory.Index haven't used it yet but will when we talk about the index of a subgroup
import Mathlib.Data.Finset.Card -- used for Sylow Thm about existence p | |G|
import Mathlib.GroupTheory.OrderOfElement -- includes orderOf used for p_subgroup_3
import Mathlib.Data.Nat.Choose.Basic -- contains Nat.choose
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Nat.Choose.Dvd


-- Basic examples

#eval 5 ≡ 8 [MOD 3]

example : 5 ≡ 8 [MOD 3] := by
rfl

#eval Nat.choose 5 2

example: Nat.choose 4 2 = 6 := by
rfl
done


-- First we define key terms or just import them

section Definitions

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] -- decided to define variable first so we don't have to


/-- A finite p-group is a finite group in which every element has prime power order -/
def p_subgroup_1: Prop := -- this one was in the Sylow.lean
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

def p_subgroup_2 : Prop := -- somehow this definitions doesn't work when we tried using it in Sylow structure
 ∃ n : ℕ, Fintype.card G = p ^ n

def p_subgroup_3 : Prop := -- the best option we found
∀ g : G, ∃ n : ℕ, orderOf g = p^n

 #check p_subgroup_3

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  p_subgroup_3' : p_subgroup_3 p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_3 p Q → toSubgroup ≤ Q → Q = toSubgroup

#check Sylow p G

def issylow (K : Subgroup G) : Prop := -- this one didn't work in the Sylow Thm about existence
∀ k : K, ∃ n : ℕ, orderOf k = p ^ n ∧ ∀ (Q : Subgroup G), p_subgroup_3 p Q → K ≤ Q → Q = K

-- Define the conjugate subgroup of H by g




--Below we state the theorems
section Sylow_Statements

-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem existence_one (hdvd : p ∣ Fintype.card G) (Q : Subgroup G) : Sylow p Q := by
sorry
done

section Sylow_1_Necessary_Lemmas_Wielandt

-- Lemma 3.3 page 36 Intro to Group Theory i)
lemma binomial_codfseff_prop1 {n m : ℕ} (hp : Nat.gcd m p = 1) : Nat.choose (m * p ^ n) (p ^ n) ≡ m [MOD p] := by
sorry
done

#check binomial_codfseff_prop1

-- Lemma 3.3 page 36 Intro to Group Theory ii)
lemma binomial_coefsadf_prop2 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
apply Nat.Prime.dvd_choose hp

exact h.right

have h': p+1 ≤ p+i
apply add_le_add_left
apply h.left
exact Nat.add_one_le_iff h'

apply le_refl
done

#check binomial_coefsadf_prop2

section Sylow_2_3_Necessary_for_Proofs

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := ⟨1, H.one_mem, by simp⟩
  mul_mem' :=
  inv_mem' :=

def conjugate123 {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G :=
  { carrier := {a : G | ∃ h ∈ H, a = x * h * x⁻¹},
    one_mem' := by sorry,
    mul_mem' := by sorry,
    inv_mem' := by sorry
  }

variable (P : Sylow p G)
#check conjugate123 _ P

--Proposition 3.5 page 39 Intro to Group Theory I don't how to write gPg^-1 so that lean understands
theorem notsure (hdvd : p ∣ Fintype.card G) (H : Subgroup G) (P : Sylow p G): ∃ (g : G), Sylow p (H ⊓ (conjugate_subgroup P g)) := by
sorry
done

-- def conjugate_of_subgroup (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (g : G) : Subgroup G :=
-- { carrier := g * H * g⁻¹,
--   one_mem' := by simp,
--   mul_mem' := fun a b ha hb => by simp [mul_assoc, ha, mul_assoc.symm, hb]
--   inv_mem' := fun a ha => by simp [mul_assoc.symm, ha, mul_assoc] }

#where
