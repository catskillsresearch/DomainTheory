module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace Cofinite
section

open NeighborhoodSystem

def cofiniteSystem : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]
    exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem cofiniteSystem_mem {X : Set ℕ} : cofiniteSystem.mem X ↔ Xᶜ.Finite := Iff.rfl

def ofExcluded (E : Set ℕ) : cofiniteSystem.Element where
  mem Y := Yᶜ.Finite ∧ Yᶜ ⊆ E
  sub h := h.1
  master_mem := by
    show (Set.univ : Set ℕ)ᶜ.Finite ∧ (Set.univ : Set ℕ)ᶜ ⊆ E
    rw [Set.compl_univ]
    exact ⟨Set.finite_empty, Set.empty_subset E⟩
  inter_mem := by
    rintro Y1 Y2 ⟨hf1, hs1⟩ ⟨hf2, hs2⟩
    rw [Set.compl_inter]
    exact ⟨hf1.union hf2, Set.union_subset hs1 hs2⟩
  up_mem := by
    rintro Y1 Y2 ⟨_, hs1⟩ hY2 hsub
    exact ⟨hY2, (Set.compl_subset_compl.mpr hsub).trans hs1⟩

@[simp] theorem mem_ofExcluded {E Y : Set ℕ} :
    (ofExcluded E).mem Y ↔ Yᶜ.Finite ∧ Yᶜ ⊆ E := Iff.rfl

def toExcluded (x : cofiniteSystem.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

@[simp] theorem mem_toExcluded {x : cofiniteSystem.Element} {n : ℕ} :
    n ∈ toExcluded x ↔ x.mem ({n}ᶜ) := Iff.rfl

def fullSystem : NeighborhoodSystem ℕ where
  mem _ := True
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := trivial
  inter_mem := fun _ _ _ _ => trivial
  sub_master := fun _ => Set.subset_univ _

theorem mem_compl_of_finite (x : cofiniteSystem.Element) {F : Set ℕ} (hF : F.Finite) :
    (∀ n ∈ F, x.mem ({n}ᶜ)) → x.mem (Fᶜ) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ _ ih =>
    intro h
    rw [Set.insert_eq, Set.compl_union]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

theorem mem_compl_singleton (n : ℕ) : cofiniteSystem.mem (({n} : Set ℕ)ᶜ) := by
  rw [cofiniteSystem_mem, compl_compl]
  exact Set.finite_singleton n

theorem subset_compl_singleton {Y : Set ℕ} {n : ℕ} (hn : n ∈ Yᶜ) : Y ⊆ ({n} : Set ℕ)ᶜ := by
  intro m hm
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact hn hm

theorem ofExcluded_toExcluded (x : cofiniteSystem.Element) :
    ofExcluded (toExcluded x) = x := by
  apply Element.ext
  intro Y
  rw [mem_ofExcluded]
  constructor
  · rintro ⟨hfin, hsub⟩
    have h := mem_compl_of_finite x hfin (fun n hn => mem_toExcluded.mp (hsub hn))
    rwa [compl_compl] at h
  · intro hxY
    refine ⟨x.sub hxY, ?_⟩
    intro n hn
    rw [mem_toExcluded]
    exact x.up_mem hxY (mem_compl_singleton n) (subset_compl_singleton hn)

theorem toExcluded_ofExcluded (E : Set ℕ) : toExcluded (ofExcluded E) = E := by
  ext n
  rw [mem_toExcluded, mem_ofExcluded]
  simp [compl_compl, Set.finite_singleton, Set.singleton_subset_iff]

def cofiniteIso : cofiniteSystem.Element ≃o Set ℕ where
  toFun := toExcluded
  invFun := ofExcluded
  left_inv := ofExcluded_toExcluded
  right_inv := toExcluded_ofExcluded
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h Y hY
      have hfin : Yᶜ.Finite := x.sub hY
      have hsub : Yᶜ ⊆ toExcluded x' := by
        intro n hn
        have hx : x.mem (({n} : Set ℕ)ᶜ) :=
          x.up_mem hY (mem_compl_singleton n) (subset_compl_singleton hn)
        exact h (mem_toExcluded.mpr hx)
      have h2 := mem_compl_of_finite x' hfin (fun n hn => mem_toExcluded.mp (hsub hn))
      rwa [compl_compl] at h2
    · intro h n hn
      exact mem_toExcluded.mpr (h _ (mem_toExcluded.mp hn))

theorem le_ofExcluded_univ (x : cofiniteSystem.Element) :
    x ≤ ofExcluded Set.univ := by
  intro Y hY
  exact ⟨x.sub hY, Set.subset_univ _⟩

theorem ofExcluded_univ_isTotal : cofiniteSystem.IsTotal (ofExcluded Set.univ) :=
  fun y _ => le_ofExcluded_univ y
end

end Cofinite
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Cofinite
section

set_option linter.unusedVariables false

theorem example_116 : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
  DomainTheory.NeighbourhoodSystems.Cofinite.cofiniteSystem
  (DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded (@Set.univ Nat)) :=
  DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded_univ_isTotal
end

end DomainTheory.NeighbourhoodSystems.Cofinite
end
