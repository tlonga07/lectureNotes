// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(n >= 0), //precondition
    Ensures(Res[Z] == n*(n+1))
  )

  var sum: Z = 0
  var cur: Z = 0

  //must prove invariant before loop begins
  Deduce(
    1 ( sum == 0 ) by Premise,
    2 ( cur == 0 ) by Premise,
    3 ( sum == cur*(cur+1) ) by Algebra*(1,2) //proves invariant before loop begins
  )

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur,sum),
      sum == cur*(cur+1) //invariant
    )

    cur = cur + 1

    //process variable change
    Deduce(
      1 ( cur == Old(cur) + 1 ) by Premise, //from assignment
      //2 ( Old(cur) == 0 ) by Premise //NO!! Not true at the beginning of all iterations, so can't say
      2 ( Old(cur) != n ) by Premise, //loop condition is true
      3 ( Old(cur) == cur - 1 ) by Algebra*(1),
      4 ( sum == Old(cur)*(Old(cur)+1) ) by Premise, //invariant was true at the beginning of iteration
      5 ( sum == (cur-1)*((cur-1)+1) ) by Algebra*(3,4) //processes invariant without using Old 
    )

    sum = sum + 2*cur

    //prove invariant still holds here
    Deduce(
      1 ( Old(sum) == (cur-1)*((cur-1)+1) ) by Premise, //shown in previous block
      2 ( sum == Old(sum) + 2*cur ) by Premise, //from assignment
      3 ( sum == (cur-1)*((cur-1)+1) + 2*cur ) by Algebra*(1,2),
      4 ( sum == (cur-1)*cur + 2*cur ) by Algebra*(3),
      5 ( sum == cur*cur - cur + 2*cur ) by Algebra*(4),
      6 ( sum == cur*cur + cur ) by Algebra*(5),
      7 ( sum == cur*(cur+1) ) by Algebra*(6) //proves invariant
      //goal: sum == cur*(cur+1)
    )
  }

  //prove postconditoin
  Deduce(
    1 ( !(cur != n ) ) by Premise, //condition is false
    2 ( cur == n ) by Algebra*(1),
    3 ( sum == cur*(cur+1) ) by Premise, //invariant is true
    4 ( sum == n*(n+1) ) by Algebra*(2,3) //proves postcondition
    //need: sum == n*(n+1)
  )

  return sum
}

//////////// test code /////////

val num: Z = 5

//prove its precondition
Deduce(
  1 ( num == 5 ) by Premise,
  2 ( num >= 0 ) by Algebra*(1) //proves precondition
)

var sum5evens: Z = sumEvens(num)

Deduce(
  1 ( sum5evens == num*(num+1) ) by Premise, //postcondition is true
  2 ( num == 5 ) by Premise,
  3 ( sum5evens == 30 ) by Algebra*(1,2)
)

//sum of first 5 evens: ?
assert(sum5evens == 30)