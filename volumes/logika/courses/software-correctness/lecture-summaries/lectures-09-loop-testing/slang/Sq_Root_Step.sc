// #Sireum #Logika
import org.sireum._

var n: Z = randomInt()
var x: Z = 0
var y: Z = n + 1

def sq_root_step() {
  Contract(
    Requires(
      x * x <= n, // Lower bound invariant
      n < y * y), // Upper bound invariant
    Modifies(x, y),
    Ensures(x * x <= n, n < y * y)
  )
  val z: Z = (x + y) / 2
  if (z * z <= n) {
    x = z
  } else {
    y = z
  }
}

def sq_root_step_unfold() {
  Contract(
    Modifies(x, y)
  )
  val z: Z = (x + y) / 2
  if (z * z <= n) {
    x = z
  } else {
    y = z
  }
}

def sq_root_lb() {
  Contract(
    Requires(x * x <= n),
    Modifies(x, y),
    Ensures(x * x <= n)
  )
  // For sq_root_step the precondition is not satisfied
  sq_root_step_unfold()
}

def sq_root_ub() {
  Contract(
    Requires(n < y * y),
    Modifies(x, y),
    Ensures(n < y * y)
  )
  // For sq_root_step the precondition is not satisfied
  sq_root_step_unfold()
}

def sq_root_lb_ub() {
  Contract(
    Requires(x * x <= n),
    Modifies(x, y),
    Ensures(x * x <= n, n < y * y)
  )
  // For sq_root_step the precondition is not satisfied
  sq_root_step_unfold()
}
