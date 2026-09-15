// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orComm(p: B, q: B): Unit = {
    Deduce(
        (p | q) |- (q | p)
        Proof(
            //PROOF GOES HERE
            1 ( p | q )     by Premise,

            //use OrE subproofs

            //case where p is true
            //show that q | p is true
            2 SubProof(
                3 Assume ( p ),
                4 ( q | p ) by OrI2(3)
            ),
            5 SubProof(
                6 Assume ( q ),
                7 ( q | p ) by OrI1(6)
            ),
            //claim my common conclusion
            //OrE line numbers:
                //OrE(originalOr, )
            8 ( q | p ) by OrE(1, 2, 5)
            
            //case where q is true
                //show that q | p is true
        )
    )
}