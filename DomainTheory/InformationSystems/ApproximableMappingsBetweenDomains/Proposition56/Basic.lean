module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap

@[expose] public section

/-!
# Proposition 5.6 — constant approximable mappings

**Scott 1982, Proposition 5.6.** For a fixed element `b ∈ |B|` there is a unique
approximable map `const b : A → B` with `(const b)(x) = b` for all `x`. Moreover
`f ∘ (const b) = const (f(b))` and `(const b) ∘ g = const b`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
