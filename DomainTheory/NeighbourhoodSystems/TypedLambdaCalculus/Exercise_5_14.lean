module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_13

public import Mathlib.Data.Set.Defs

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

def tag : List ℕ → ℕ → ℕ
  | [], m => num 0 m
  | (n :: ns), m => num (n + 1) (tag ns m)

end DomainTheory.NeighbourhoodSystems.Exercise514
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise514
open DomainTheory.NeighbourhoodSystems.Exercise513

section
@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl
end

section
@[simp] theorem tag_cons (n : ℕ) (ns : List ℕ) (m : ℕ) :
    tag (n :: ns) m = num (n + 1) (tag ns m) := rfl
end

section

def entries (ns : List ℕ) : Set ℕ := {n | n ∈ ns}
end

section
@[simp] theorem mem_entries {n : ℕ} {ns : List ℕ} : n ∈ entries ns ↔ n ∈ ns := Iff.rfl
end

section

def Fun (u : Set ℕ) (x : Set ℕ) : Set ℕ :=
  {m | ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}
end

section

def Graph (f : Set ℕ → Set ℕ) : Set ℕ :=
  {c | ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}
end

section

def IsApprox (f : Set ℕ → Set ℕ) : Prop :=
  (∀ ⦃x x' : Set ℕ⦄, x ⊆ x' → f x ⊆ f x') ∧
    ∀ x m, m ∈ f x → ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ m ∈ f (entries ns)
end

section

theorem Fun_isApprox (u : Set ℕ) : IsApprox (Fun u) := by
  refine ⟨?_, ?_⟩
  · intro x x' hxx' m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, fun n hn => hxx' (hsub n hn), htag⟩
  · intro x m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, hsub, ns, fun n hn => hn, htag⟩
end

section

theorem Fun_mono {u u' x x' : Set ℕ} (hu : u ⊆ u') (hx : x ⊆ x') : Fun u x ⊆ Fun u' x' := by
  rintro m ⟨ns, hns, htag⟩
  exact ⟨ns, fun n hn => hx (hns n hn), hu htag⟩
end

section

theorem num_succ_left_gt (n b : ℕ) : b < num (n + 1) b := by
  unfold num
  have e : n + 1 + b = (n + b) + 1 := by omega
  rw [e, tri_succ]
  omega
end

section

theorem tag_injective : ∀ {ns₁ ns₂ : List ℕ} {m₁ m₂ : ℕ},
    tag ns₁ m₁ = tag ns₂ m₂ → ns₁ = ns₂ ∧ m₁ = m₂ := by
  intro ns₁
  induction ns₁ with
  | nil =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          have hp := num_injective (show numP (0, m₁) = numP (0, m₂) from h)
          injection hp with _ hm
          exact ⟨rfl, hm⟩
      | cons n₂ ns₂' =>
          exfalso
          have hp := num_injective (show numP (0, m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 _
          omega
  | cons n₁ ns₁' ih =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          exfalso
          have hp := num_injective (show numP (n₁ + 1, tag ns₁' m₁) = numP (0, m₂) from h)
          injection hp with h1 _
          omega
      | cons n₂ ns₂' =>
          have hp := num_injective
            (show numP (n₁ + 1, tag ns₁' m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 h2
          have hn : n₁ = n₂ := by omega
          obtain ⟨hns, hm⟩ := ih h2
          exact ⟨by rw [hn, hns], hm⟩
end

section

theorem Fun_Graph {f : Set ℕ → Set ℕ} (hf : IsApprox f) (x : Set ℕ) :
    Fun (Graph f) x = f x := by
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    obtain ⟨ns', m', heq, hmem⟩ := htag
    obtain ⟨hns, hmm⟩ := tag_injective heq
    subst hns; subst hmm
    have hsubset : entries ns ⊆ x := fun n hn => hsub n hn
    exact hf.1 hsubset hmem
  · intro m hm
    obtain ⟨ns, hsub, hmem⟩ := hf.2 x m hm
    exact ⟨ns, hsub, ns, m, rfl, hmem⟩
end

section

theorem tag_surjective (c : ℕ) : ∃ ns m, tag ns m = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      obtain ⟨a, b, hab⟩ : ∃ a b, num a b = c :=
        ⟨(unnum c).1, (unnum c).2, numP_unnum c⟩
      cases a with
      | zero => exact ⟨[], b, hab⟩
      | succ k =>
          have hlt : b < c := by rw [← hab]; exact num_succ_left_gt k b
          obtain ⟨ns, m, hns⟩ := ih b hlt
          exact ⟨k :: ns, m, by rw [tag_cons, hns]; exact hab⟩
end

section

theorem id_le_Graph_Fun (u : Set ℕ) : u ⊆ Graph (Fun u) := by
  intro c hc
  obtain ⟨ns, m, hceq⟩ := tag_surjective c
  refine ⟨ns, m, hceq.symm, ?_⟩
  exact ⟨ns, fun n hn => hn, by rw [hceq]; exact hc⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise514
end
