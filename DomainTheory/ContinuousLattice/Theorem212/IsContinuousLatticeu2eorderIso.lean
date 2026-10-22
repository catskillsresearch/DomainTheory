/-ai
Continuous-lattice structure transfers across an order isomorphism: if the codomain is a continuous lattice, so is the domain.

Every element way below a given element lies below it. If an element b lies above every element way below y, the order isomorphism reduces y ≤ b to the corresponding inequality of images. Continuity of the codomain says the image of y lies below the image of b once every element way below the image of y does. The inverse image of such an element is way below y, by preservation of way-below under the inverse isomorphism, hence lies below b, and monotonicity of the isomorphism returns the desired inequality.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic
public import DomainTheory.ContinuousLattice.Theorem212.orderIso_wayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set


universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- Continuous-lattice structure transfers across an order isomorphism. -/
theorem orderIso (e : A ≃o B) (hB : ContinuousLattice B) :
    ContinuousLattice A := by
  constructor
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  apply e.le_iff_le.mp
  exact (hB.out (e y)).2 fun z hz => by
    have hz' : e.symm z ≪ y := by
      simpa using orderIso_wayBelow e.symm hz
    have := hb hz'
    simpa using e.monotone this

end Theorem212Transfer
end DomainTheory.ContinuousLattice
