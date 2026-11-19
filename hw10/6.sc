// #Sireum #Logika
//@Logika: --manual

//YOU DO THIS
//Add proof blocks in the sumUp function and the test code
//When you finish, the assert statement should be verified

//You should not make any changes other than adding proof blocks

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def sumUp(n: Z): Z = {
  Contract(
    Requires ( n >= 1, 2 != 0 ),
    Ensures (Res[Z] == n*(n+1)/2)
  )

  var sum: Z = 0
  var i: Z = 0
    
    Deduce(
        1 ( sum == 0 ) by Premise,
        2 ( i == 0 ) by Premise,
        3 ( 2 != 0 ) by Premise,
        4 ( sum == i*(i+1)/2 ) by Algebra*(1,2,3)
    )
  //the invariant holds before the loop begins
  //(you need to prove this)
  assert(sum == i * (i+1)/2)

  while (i != n) {
    Invariant(
      Modifies(sum, i),
      sum == (i * (i+1))/2
    )

    i = i + 1
    Deduce(
        1 ( i == Old(i)+1 ) by Premise,
        2 ( sum == Old(i)*(Old(i)+1)/2 ) by Premise,
        3 ( sum == (i-1)*i/2 ) by Algebra*(1,2)
    )
    sum = sum + i

    Deduce(
        1 ( sum == Old(sum)+i ) by Premise,
        2 ( Old(sum) == (i-1)*i/2 ) by Premise,
        3 ( 2 != 0 ) by Premise,
        4 ( sum == (i-1)*i/2+i ) by Algebra*(1,2),
        5 ( sum == i*(i+1)/2 ) by Algebra*(3,4)
    )
    //the invariant holds at the end of the iteration
    //(you need to prove this)
    assert(sum == i * (i+1)/2)
  }
  Deduce(
    1 ( sum == i*(i+1)/2 ) by Premise,
    2 ( !(i != n) ) by Premise,
    3 ( i == n ) by Algebra*(2),
    4 ( sum == n*(n+1)/2 ) by Algebra*(1,3)
   )
  return sum
}

//////////// Test code /////////////

var num: Z = 6

Deduce(
    1 ( num == 6 ) by Premise,
    2 ( num >= 1 ) by Algebra*(1),
    3 ( 2 != 0 ) by Algebra*(1)
)
val sumTo6: Z = sumUp(num)

Deduce(
    1 ( sumTo6 == num*(num+1)/2 ) by Premise,
    2 ( num == 6 ) by Premise,
    3 ( 2 != 0 ) by Premise,
    4 ( sumTo6 == 21 ) by Algebra*(1,2,3)
)
println("The sum from 1 up to 6 is ", sumTo6)

assert(sumTo6 == 21)