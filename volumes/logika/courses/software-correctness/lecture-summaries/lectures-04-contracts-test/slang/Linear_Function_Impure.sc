// #Sireum #Logika
import org.sireum._

// linmap yields a * x + b for any a, x, and b
def linmap(a: Z, x: Z, b: Z): Z = {
  Contract(
    Ensures(Res == a * x + b)
  )
  return a * x + b
}

// given (x - b) % a == 0 revmap yields (x - b) / a for any a, x, and b
def revmap(a: Z, x: Z, b: Z): Z = {
  Contract(
    Requires(a != 0, (x - b) % a == 0),
    Ensures(Res == (x - b) / a)
  )
  return (x - b) / a
}

// compose yields x for any a, x, and b
def compose(a: Z, x: Z, b: Z): Z = {
  Contract(
    Requires(a != 0),
    Ensures(Res == x)
  )
  var y: Z = linmap(a, x, b)
  Deduce(|- (y == a * x + b))
  y = revmap(a, y, b)
  Deduce(|- (a != 0))
  Deduce(|- ((a * x + b - b) % a == 0))
  Deduce(|- (At(y, 0) == a * x + b))
  Deduce(|- (y == ((At(y, 0) - b) / a)))
  Deduce(|- (y == ((a * x + b - b) / a)))
  return y
}