module Shape_abs

export
data Shape : Type where
  Triangle : (base : Double) -> (height : Double) -> Shape
  Rectangle : (length : Double) -> (height : Double) -> Shape
  Circle : (radius : Double) -> Shape

export
triangle : (base : Double) -> (height : Double) -> Shape
triangle = Triangle

export
rectangle : (length : Double) -> (height : Double) -> Shape
rectangle = Rectangle

export
circle : (radius : Double) -> Shape
circle = Circle

public export
data ShapeView : Shape -> Type where
     STriangle : ShapeView (triangle base height)
     SRectangle : ShapeView (rectangle length height)
     SCircle : ShapeView (circle radius)

export
shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle base height) = STriangle
shapeView (Rectangle length height) = SRectangle
shapeView (Circle radius) = SCircle
