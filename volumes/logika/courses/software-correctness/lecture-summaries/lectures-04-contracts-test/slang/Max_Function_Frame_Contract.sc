// #Sireum #Logika
import org.sireum._

var z: Z = 0

def max(x: Z, y: Z) {
  Contract(
    Requires(x > 0, y > 0),
    Modifies(z),
    Ensures(z == x | z == y, x <= z, y <= z)
  )
  if (x < y) {
    z = y
  } else {
    z = x
  }
}