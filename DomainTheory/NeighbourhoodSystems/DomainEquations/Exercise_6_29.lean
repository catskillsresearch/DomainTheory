module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.infSumProd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise629
open NeighborhoodSystem

theorem example_629 :
    (∀ {ι : Type*} {α : ι → Type*} [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) (W : Set (Σ i, α i)),
        (iotimes D).mem W → W = (iotimes D).master) ∧
    (∀ {ι : Type*} {α : ι → Type*} [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)),
      Subsingleton (iotimes D).Element) ∧
    (∀ {ι : Type*} {α : ι → Type*} {D : ∀ i, NeighborhoodSystem (α i)}
        {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty} (z : (isum D hne).Element)
        {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      z.mem (injI i X) → z.mem (injI j Y) → i = j) ∧
    (∀ {ι : Type*} {α : ι → Type*} {D : ∀ i, NeighborhoodSystem (α i)}
        {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty} (z : (isum D hne).Element),
      (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
        (∀ W, z.mem W → W = (isum D hne).master)) :=
  ⟨@iotimes_only_master, @iotimes_subsingleton, @isum_summand_unique, @isum_trichotomy⟩

end DomainTheory.NeighbourhoodSystems.Exercise629
