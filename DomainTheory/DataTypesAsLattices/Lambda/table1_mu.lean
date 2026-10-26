module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.mu_law
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Table 1 (μ).** Application is monotone. -/
theorem table1_mu {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  mu_law hu hx

end DomainTheory.DataTypesAsLattices
