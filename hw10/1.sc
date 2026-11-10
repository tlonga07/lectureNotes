// #Sireum #Logika
//@Logika: --manual

//YOU DO THIS
//Add proof blocks in the minus function and the test code
//When you finish, the assert statements should be verified

//You should not make any changes other than adding proof blocks

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def fourTimes(x: Z, y: Z): Z = {
  Contract(
    Requires(x == y & y > 0),
    Ensures(
      Res[Z] == 4*x,
      Res[Z] >= 4
    )
  )

  var sub: Z = x + y
  sub = sub * 2
  return sub
}

//////////// Test code (asserts should hold when you finish) /////////////

val a: Z = Z.read()
val b: Z = Z.read()

assume(a == 4)
assume(b > 4 & b < 6)

//a must equal b - 1 
//b - 1 must be greater that 0? 
Deduce(
    1 ( a == 4 ) by Premise, 
    2 ( b > 4 & b < 6 ) by Premise,
    3 ( b > 4 ) by AndE1, 
    4 ( b < 6 ) by AndE2, 

    5 ( b == 5 ) by Algebra*(3, 4),
    6 ( b - 1 == 4 ) by Algebra*(5),
    7 ( a == b - 1 ) by Algebra*(1, 6), 
    8 ( b - 1 > 0 ) by Algebra*(6),
    9 ( a == b - 1 & b - 1 > 0 ) by AndI(7, 8)
)

assert(a == b - 1 & b - 1 > 0)//assert cus of deduce block 

var test: Z = fourTimes(a, b-1)
assert(test == 16)


/////////

val j: Z = 7
val k: Z = 4

test = fourTimes(j-3, k)
assert(test == 16)