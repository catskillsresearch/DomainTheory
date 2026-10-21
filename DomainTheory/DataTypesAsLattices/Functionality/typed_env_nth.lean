/-ai
If an environment t is typed by the environment retract, then its application to the numeral n is typed by the lambda retract.

The typing, rewritten by the environment retract equation, says that t equals the graph of the map sending m to the lambda retract applied to the application of t at m. Substituting that graph, beta reduction for the composite of the two continuous application maps yields that the application of t at the numeral equals the lambda retract applied to itself, which is the required typing.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.envR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_env_nth {t : Pomega} (ht : typed t envR) (n : ℕ) :
    typed (funOf t (ofNat n)) lambR := by
  have ht' : t = graph (fun m => funOf lambR (funOf t m)) := by
    simpa [typed, envR_app] using ht
  have : funOf t (ofNat n) = funOf lambR (funOf t (ofNat n)) := by
    nth_rw 1 [ht']
    exact beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) (ofNat n)
  exact this

end DomainTheory.DataTypesAsLattices
