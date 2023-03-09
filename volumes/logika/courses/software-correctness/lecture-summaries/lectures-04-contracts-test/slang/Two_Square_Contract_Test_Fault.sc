// #Sireum #Logika
import org.sireum._

var x: Z = randomInt()
var y: Z = randomInt()

def tsq() {
  Contract(
    Modifies(x, y),
    Ensures(x >= 0, y >= 0)
  )
  x = x * x
  y = y + y // correct: y = y * y
  if (x < y) {
    y = y - x
  } else {
    x = x - y
  }
}

// Unsatisfiable "(At(x, 1) < At(y, 1))"
// At(x, 1) == At(x, 0) * At(x, 0) &
// At(y, 1) == At(y, 0) + At(y, 0) &
// (At(x, 1) < At(y, 1)) &
// (At(x, 1) < At(y, 1)) -> (x == At(x, 1)) &
// (At(x, 1) < At(y, 1)) -> (y == At(y, 1) - x) &
// y < 0

// Branch with counterexample "!(At(x, 1) < At(y, 1))"
// At(x, 1) == At(x, 0) * At(x, 0) &
// At(y, 1) == At(y, 0) + At(y, 0) &
// !(At(x, 1) < At(y, 1)) &
// !(At(x, 1) < At(y, 1)) -> (y == At(y, 1)) &
// !(At(x, 1) < At(y, 1)) -> (x == At(x, 1) - y) &
// y < 0

// Compare symbolic execution!