// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//Complete the following natural deduction proof.
//When you are finished, run a Logika check -- your file should say "Logika verified".


//∃ x (ksu(x) ∨ ku(x)), ¬(∃ x ku(x)) ⊢ ∃ x ksu(x)

@pure def proof1[T](ksu: T=>B @pure, ku: T=>B @pure): Unit = {
  Deduce(
    (
      ∃((x: T) => (ksu(x) | ku(x))),
      !(∃((x: T) => ku(x)))
    )
      |-
    (
      ∃((x: T) => ksu(x))
    )
    Proof(
        1 ( ∃((x: T) => (ksu(x) | ku(x))) ) by Premise,
        2 ( !(∃((x: T) => ku(x))) ) by Premise, 
        3 Let ((a: T) => SubProof( 
            4 Assume (ksu(a) | ku(a)), 

            5 SubProof(
                6 Assume (ku(a)), 
                7 ( ∃((x: T) => ku(x)) ) by ExistsI[T](6),
                8 ( F ) by NegE(7, 2)

            ),
            9 (!ku(a)) by NegI(5), 

            10 SubProof(
                11 Assume(ksu(a)),
                12 ( ∃((x: T) => ksu(x)) ) by ExistsI[T](11)
            ),

            13 SubProof(
                14 Assume (ku(a)),

                15 SubProof(
                    16 Assume(!ksu(a)),
                    17 ( F ) by NegE(14, 9)
                ),
                18 (ksu(a)) by PbC(15),
                19 ( ∃((x: T) => ksu(x)) )  by ExistsI[T](18)
            ),
            20 ( ∃((x: T) => ksu(x)))  by OrE(4, 10, 13)
        )),
        21 ( ∃((x: T) => ksu(x))) by ExistsE[T](1, 3)


        //COMPLETE PROOF HERE

    )
  )
  
}