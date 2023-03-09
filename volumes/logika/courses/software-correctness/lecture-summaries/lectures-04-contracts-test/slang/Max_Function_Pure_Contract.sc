// #Sireum #Logika
import org.sireum._

def max(x: Z, y: Z): Z = {
  Contract(
    Requires(x > 0, y > 0),
    Ensures(Res == x | Res == y, x <= Res, y <= Res)
  )
  if (x < y) {
    return y
  } else {
    return x
  }
}
