// #Sireum #Logika
//@Logika: --manual

//YOU DO THIS
//FIRST, write a function contract that promises that findMin returns the smallest of its two parameters.
//NEXT, add proof blocks in the findMin function and the test code
//When you finish, the assert statement should be verified

//You should not make any changes other than adding the function contract and the proof blocks


import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def findMin(x: Z, y: Z): Z = {
  //ADD FUNCTION CONTRACT
    Contract(
    Requires(
        
    ),
    Ensures(
      Res[Z] <= x,
      Res[Z] <= y,
      Res[Z] == x | Res[Z] == y
    )
    )
  var min: Z = 0

  if (x <= y) {
    min = x
    Deduce(
        1 ( min == x ) by Premise, 
        2 ( x <= y ) by Premise,

        3 ( min <= x ) by Algebra*(1, 2), 
        4 ( min <= y ) by Algebra*(2, 3),
        5 (min == x | min == y) by OrI1(1)
    )
  } else {
    min = y
    Deduce(
        1 ( min == y ) by Premise, 
        2 ( !(x <= y) ) by Premise, 
        3 ( min <= x ) by Algebra*(1, 2), 
        4 ( min <= y ) by Algebra*(1), 

        5 (min == x | min == y) by OrI2(1)
    )
  }
  Deduce (
    1 ( min <= x ) by Premise, 
    2 ( min <= y ) by Premise,
    3 (min == x | min == y) by Premise
  )

  return min
}

//////////// Test code (assert should hold when you finish) /////////////

val num1: Z = 6
val num2: Z = 4



val small: Z = findMin(num1, num2)

Deduce(
    1 ( num1 == 6 ) by Premise, 
    2 ( num2 == 4 ) by Premise, 

    3 ( small <= num1 ) by Premise, 
    4 ( small <= num2 ) by Premise, 

    5 (small == num1 | small == num2) by Premise,
    6 (small <= 4) by Algebra*(2, 4),
    7 (small == 6 | small == num2) by Subst_<(1, 5),
    8 ( small == 6 | small == 4) by Subst_<(2, 7), 
    
    9 SubProof(
        10 Assume(small == 6),
        11 SubProof(
            12 Assume ( !(small ==4 ) ),
            13 ( F ) by Algebra*(6, 10)
        ),
        14 ( small == 4 ) by PbC(11)
    ),
    15 SubProof(
        16 Assume ( small == 4 ),
        17 ( small == 4 ) by Premise
    ),
    18 ( small == 4 ) by OrE(8, 9, 15)

    
        
    





)

assert(small == 4)