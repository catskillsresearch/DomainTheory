/-ai
The image subdomain determined by a pair of approximable maps is the neighbourhood system on the codomain token type whose neighbourhoods are the sets that generate some set under those maps, and whose master is the master of the codomain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The image subdomain `D'`.** A `β`-set `Y` is a neighbourhood iff it generates some
`D`-neighbourhood; the master is `E`'s master. `isGen_inter` supplies condition (ii). -/
def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
