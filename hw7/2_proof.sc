// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//Complete the following natural deduction proof.
//When you are finished, run a Logika check -- your file should say "Logika verified".

//∀ x (student(x) → csharp(x)), ∃ x ¬csharp(x) ⊢ ∃ x ¬student(x)

@pure def proof2[T](student: T=>B @pure, csharp: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (student(x) __>: csharp(x))),
      ∃((x: T) => !csharp(x))
    )
      |-
      (
        ∃((x: T) => !student(x))
      )
      Proof(
        1 ( ∀((x: T) => (student(x) __>: csharp(x))) )by Premise,
        2 ( ∃((x: T) => !csharp(x)) ) by Premise,

        3 Let ((a: T) => SubProof(
            4 Assume(!csharp(a)), //assume there is a student that doesnt know csharp and get ∃((x: T) => !student(x)) by ExistsEliminateion

            5 ( student(a) __>: csharp(a) ) by AllE[T](1), 

            6 SubProof( //prove a not a student 
                7 Assume (student(a)),
                8 (csharp(a)) by ImplyE(5, 7),
                9 ( F ) by NegE(8, 4)
            ), 
            10 (!student(a)) by NegI(6),
            11 ( ∃((x: T) => !student(x))) by ExistsI[T](10)
        )),
        12  ( ∃((x: T) => !student(x))) by ExistsE[T](2, 3)
        //COMPLETE PROOF HERE

      )
  )
}