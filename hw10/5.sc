// #Sireum #Logika
//@Logika: --manual

//YOU DO THIS
//Add proof blocks in the subByOnes function and the test code
//When you finish, the assert statements should be verified

//You should not make any changes other than adding proof blocks

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//subtraction by ones
def subByOnes(a: Z, b: Z): Z = {
  Contract(
    Requires( b >= 0 ),
    Ensures( Res[Z] == a-b)
  )

  var answer: Z = a
  var i: Z = 0

   Deduce(
    1 ( answer == a ) by Premise, 
    2 ( i == 0 ) by Premise, 
    3 ( answer == a - i ) by Algebra*(1, 2)
   )
  //the invariant holds before the loop begins
  //(you need to prove this)
  assert(answer == a - i)

  while (i != b) {
    Invariant(
      Modifies(i, answer),
      answer == a - i
    )

    answer = answer - 1

    Deduce(
        1 ( Old(answer) == a - i ) by Premise,
        2 ( answer == Old(answer) - 1 ) by Premise,
        3 ( answer == a - i - 1 ) by Algebra*(1,2)
    )
    i = i + 1

    Deduce(
        1 ( i == Old(i) + 1 ) by Premise,
        2 ( answer == a - Old(i) - 1 ) by Premise,
        3 ( answer == a - i ) by Algebra*(1,2)
    )
    //the invariant holds at the end of the iteration
    //(you need to prove this)
    assert(answer == a - i)
  }
  Deduce(
    1 ( answer == a - i ) by Premise, 
    2 ( !( i != b ) ) by Premise, 
    3 ( i == b ) by Algebra*(2), 
    4 ( answer == a - b ) by Algebra*(1, 3)

  )

  return answer
}

//////////// These assertions should hold when you are done /////////////

var test1: Z = 10
var test2: Z = 7

Deduce(
    1 ( test2 == 7 ) by Premise,
    2 ( test2 >= 0 ) by Algebra*(1)
)

var sub: Z = subByOnes(test1, test2)

Deduce(
    1 ( sub == test1 - test2 ) by Premise,
    2 ( test1 == 10 ) by Premise,
    3 ( test2 == 7 ) by Premise,
    4 ( sub == 3 ) by Algebra*(1,2,3)
)

assert(sub == 3)
///
test1 = 2
test2 = 4

Deduce(
    1 ( test2 == 4 ) by Premise,
    2 ( test2 >= 0 ) by Algebra*(1)
)

sub = subByOnes(test1, test2)

Deduce(
    1 ( sub == test1 - test2 ) by Premise,
    2 ( test1 == 2 ) by Premise,
    3 ( test2 == 4 ) by Premise,
    4 ( sub == -2 ) by Algebra*(1,2,3)
)

assert( sub == -2)