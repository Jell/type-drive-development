import Shape_abs

area : Shape -> Double
area input with (shapeView input)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle length height) | SRectangle = length * height
  area (circle radius) | SCircle = pi * radius * radius
