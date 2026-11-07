module

public import Mathlib.Computability.Language
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace PeriodicTree
open Language


variable {n : ℕ}

abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool

def pos (a : Tree n) : Bool := a []

def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl

def child (a : Tree n) (i : Fin n) : Tree n := select a [i]

@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp

@[simp] theorem pos_select (a : Tree n) (σ : List (Fin n)) : pos (select a σ) = a σ := by
  simp [pos]

def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}

@[simp] theorem mem_treeLang {a : Tree n} {σ : List (Fin n)} : σ ∈ treeLang a ↔ a σ = true := Iff.rfl

def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite

theorem select_append (a : Tree n) (σ τ : List (Fin n)) :
    select a (σ ++ τ) = select (select a σ) τ := by
  funext ρ; simp [List.append_assoc]

theorem select_cons (a : Tree n) (i : Fin n) (σ : List (Fin n)) :
    select a (i :: σ) = select (child a i) σ := by
  funext τ; simp [child]

theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl

theorem treeLang_injective : Function.Injective (treeLang (n := n)) := by
  intro a a' h
  funext σ
  have hmem : (σ ∈ treeLang a) ↔ (σ ∈ treeLang a') := by rw [h]
  simp only [mem_treeLang] at hmem
  cases ha : a σ <;> cases ha' : a' σ <;> simp_all

theorem treeLang_select (a : Tree n) (σ : List (Fin n)) :
    treeLang (select a σ) = (treeLang a).leftQuotient σ := by
  ext τ
  simp only [mem_treeLang, select_apply, Language.mem_leftQuotient]

theorem eventuallyPeriodic_iff_isRegular (a : Tree n) :
    EventuallyPeriodic a ↔ (treeLang a).IsRegular := by
  have hcomp : (treeLang a).leftQuotient = treeLang ∘ select a :=
    funext fun σ => (treeLang_select a σ).symm
  rw [Language.isRegular_iff_finite_range_leftQuotient, hcomp, Set.range_comp]
  exact (Set.finite_image_iff (treeLang_injective.injOn)).symm

theorem isRegular_iff_exists_eventuallyPeriodic (L : Language (Fin n)) :
    L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L := by
  classical
  constructor
  · intro hL
    refine ⟨fun σ => decide (σ ∈ L), ?_, ?_⟩
    · have hlang : treeLang (fun σ => decide (σ ∈ L)) = L := by
        ext σ; simp only [mem_treeLang, decide_eq_true_eq]
      rw [eventuallyPeriodic_iff_isRegular, hlang]; exact hL
    · ext σ; simp only [mem_treeLang, decide_eq_true_eq]
  · rintro ⟨a, hEP, rfl⟩
    exact (eventuallyPeriodic_iff_isRegular a).mp hEP

end PeriodicTree
end DomainTheory.NeighbourhoodSystems
