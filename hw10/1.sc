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

  Deduce(
    1 ( Old(sub) == x + y ) by Premise,
    2 ( sub == Old(sub) * 2 ) by Premise, 
    3 ( x == y & y > 0 ) by Premise, 
    4 ( x == y ) by AndE1(3), 
    5 ( y > 0 ) by AndE2(3), 

    6 ( Old(sub) == x + x ) by Algebra*(1, 4),
    7 ( Old(sub) == 2*x ) by Algebra*(6), 
    8 ( sub == 2 * (2 * x)) by Algebra*(2, 7), 
    9 ( sub == 4*x ) by Algebra*(8), 
    10 ( sub >= 4 ) by Algebra*(4, 5, 9)
  )
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
    3 ( b > 4 ) by AndE1(2), 
    4 ( b < 6 ) by AndE2(2), 

    5 ( b == 5 ) by Algebra*(3, 4),
    6 ( b - 1 == 4 ) by Algebra*(5),
    7 ( a == b - 1 ) by Algebra*(1, 6), 
    8 ( b - 1 > 0 ) by Algebra*(6),
    9 ( a == b - 1 & b - 1 > 0 ) by AndI(7, 8)
)



var test: Z = fourTimes(a, b-1)

Deduce(
    1 ( test == 4*a ) by Premise,
    2 ( a == 4 ) by Premise,
    3 ( test == 16 ) by Algebra*(1, 2)
)

assert(test == 16)


/////////

val j: Z = 7
val k: Z = 4
//need to get x == y & y > 0
Deduce(
    1 ( j == 7 ) by Premise, 
    2 ( k == 4 ) by Premise, 
    3 ( j - 3 == k ) by Algebra*(1, 2),

    4 ( k > 0 ) by Algebra*(2),
    5 ( j - 3 == k & k > 0 ) by AndI(3, 4), 

    6 ( j - 3 == 4 ) by Algebra*(1)
)

test = fourTimes(j-3, k)

Deduce(
    1 ( test == 4 * (j - 3) ) by Premise, 
    2 ( j - 3 == 4 ) by Premise, 
    3 ( test == 16 ) by Algebra*(1, 2)
)
assert(test == 16)