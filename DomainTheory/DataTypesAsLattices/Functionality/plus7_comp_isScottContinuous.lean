/-ai
If seven maps are Scott continuous, the seven-way sum of their values is Scott continuous in the common parameter.

The graph of a family continuous in a parameter is Scott continuous in that parameter. For each fixed argument, tagged injection of the application of the corresponding map at the second component is continuous, as a composite of tagged injection, application in the function, and the given map. Nested uses of the ternary continuity theorem assemble the seven double conditionals. Each test is constant in the parameter, and the final positive branch is the constant full set.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_comp_isScottContinuous
    {f0 f1 f2 f3 f4 f5 f6 : Pomega → Pomega}
    (h0 : IsScottContinuous f0) (h1 : IsScottContinuous f1)
    (h2 : IsScottContinuous f2) (h3 : IsScottContinuous f3)
    (h4 : IsScottContinuous f4) (h5 : IsScottContinuous f5)
    (h6 : IsScottContinuous f6) :
    IsScottContinuous (fun z =>
      plus7 (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z)) :=
  graph_const_isScottContinuous
    (fun z u => plus7Body (f0 z) (f1 z) (f2 z) (f3 z) (f4 z) (f5 z) (f6 z) u)
    (fun u => by
      have htag (i : ℕ) {f : Pomega → Pomega} (hf : IsScottContinuous f) :
          IsScottContinuous (fun z =>
            tagInj i (funOf (f z) (funOf u (ofNat 1)))) :=
        theorem_1_3 (f := tagInj i)
          (g := fun z => funOf (f z) (funOf u (ofNat 1)))
          (tagInj_isScottContinuous i)
          (theorem_1_3 (f := fun w => funOf w (funOf u (ofNat 1))) (g := f)
            (funOf_isScottContinuous_left (funOf u (ofNat 1))) hf)
      exact continuous_nary
        (fun y t => dcondSet_isScottContinuous_left y t)
        (fun x t => dcondSet_isScottContinuous_mid x t)
        (fun x y => dcondSet_isScottContinuous_right x y)
        (const_isScottContinuous (funOf u (ofNat 0))) (htag 0 h0)
        (continuous_nary
          (fun y t => dcondSet_isScottContinuous_left y t)
          (fun x t => dcondSet_isScottContinuous_mid x t)
          (fun x y => dcondSet_isScottContinuous_right x y)
          (const_isScottContinuous (predSet (funOf u (ofNat 0)))) (htag 1 h1)
          (continuous_nary
            (fun y t => dcondSet_isScottContinuous_left y t)
            (fun x t => dcondSet_isScottContinuous_mid x t)
            (fun x y => dcondSet_isScottContinuous_right x y)
            (const_isScottContinuous (predSet (predSet (funOf u (ofNat 0)))))
            (htag 2 h2)
            (continuous_nary
              (fun y t => dcondSet_isScottContinuous_left y t)
              (fun x t => dcondSet_isScottContinuous_mid x t)
              (fun x y => dcondSet_isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[3] (funOf u (ofNat 0))))
              (htag 3 h3)
              (continuous_nary
                (fun y t => dcondSet_isScottContinuous_left y t)
                (fun x t => dcondSet_isScottContinuous_mid x t)
                (fun x y => dcondSet_isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[4] (funOf u (ofNat 0))))
                (htag 4 h4)
                (continuous_nary
                  (fun y t => dcondSet_isScottContinuous_left y t)
                  (fun x t => dcondSet_isScottContinuous_mid x t)
                  (fun x y => dcondSet_isScottContinuous_right x y)
                  (const_isScottContinuous (predSet^[5] (funOf u (ofNat 0))))
                  (htag 5 h5)
                  (continuous_nary
                    (fun y t => dcondSet_isScottContinuous_left y t)
                    (fun x t => dcondSet_isScottContinuous_mid x t)
                    (fun x y => dcondSet_isScottContinuous_right x y)
                    (const_isScottContinuous (predSet^[6] (funOf u (ofNat 0))))
                    (htag 6 h6) (const_isScottContinuous topElem))))))))

end DomainTheory.DataTypesAsLattices
