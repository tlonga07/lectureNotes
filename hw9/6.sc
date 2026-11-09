// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//YOU DO THIS:
//Add deduce blocks so the assert holds.

//Do not change anything in the program or assert.

val x: Z = Z.read()

assume (x >= 1 & x <= 3)

var result: Z = x

if (x == 1) {
    result = result * 6

    Deduce(
        //reach result == 6 
        1 ( x == 1 ) by Premise, 
        2 ( Old(result) == x ) by Premise,
        3 ( result == Old(result) * 6 ) by Premise,
        4 ( result == 1 * 6 ) by Algebra*(1, 2, 3),
        5 ( result == 6 ) by Algebra*(4) 
    )
} else {
    if (x == 2) {
        result = result * 3
        Deduce(
            //reach result == 6 
            1 ( x == 2 ) by Premise, 
            2 ( Old(result) == x ) by Premise,
            3 ( Old(result) == 2 ) by Subst_<(1, 2),

            4 ( result == Old(result) * 3) by Premise,
            5 ( result == 2 * 3 ) by Algebra*(3, 4),
            6 ( result == 6 ) by Algebra*(5)
        )
        //reach result == 6 

    } else {
        result = result + 3
        Deduce(
            1 ( x >= 1 & x <= 3 ) by Premise, 
            2 ( !( x == 1 ) ) by Premise, 
            3 ( !( x == 2 ) ) by Premise, 
            4 (x >= 1) by AndE1(1),
            5 (x <= 3) by AndE2(1),

            6 (x == 3) by Algebra*(2, 3, 4, 5), 
            7 ( Old(result) == x ) by Premise, 
            8 ( Old(result) == 3 ) by Algebra*(6, 7),
            9 ( result == Old(result) + 3 ) by Premise, 
            10 ( result == 3 + 3 ) by Algebra*(8, 9),
            11 ( result == 6 ) by Algebra*(10) 
        )
        //reach result == 6 
    }

    Deduce(
        1 ( result == 6 ) by Premise
    )
    //add a Deduce block here to summarize what you learned in the inner if/else
}

//add a Deduce block here to summarize what you learned in the outer if/else

Deduce(
    1 ( result == 6 ) by Premise
)
assert(result == 6)