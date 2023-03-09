// #Sireum #Logika
import org.sireum._

var x = randomInt()
var q = randomInt()

def shift(p: Z, y: Z, N: Z) {
  Contract(
    Requires(x * p + y * q == N),
    Modifies(x, q),
    Ensures(x * p + y * q == N)
  )
  x = x - y
  q = q - p // correct q = q + p
}

// At(x, 0) * p + y * At(q, 0) == N & x == At(x, 0) - y & q == At(q, 0) - p & x * p + y * q != N
// input:
//   At(x, 0) = 1  (for x)
//   At(q, 0) = 1  (for q)
//   p = 1 & y = 1 & N = 2
// we have:
//     1 * 1 + 1 * 1 == 2 & x == 1 - 1 & q == 1 - 1 & x * 1 + 1 * q != 2
// ->  2 == 2 & 0 * 1 + 1 * 0 != 2
// ->  2 == 2 & 0 != 2

// We have found a counterexample for the contract, a test case that exhibits the fault
// If the program is corrected as shown in the comment in the function, the test succeeds (as does the proof)