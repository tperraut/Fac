import java.awt.*;
import java.lang.Math;

public class Rec
{
	private Rectangle r;

	public Rec (Point p1, Point p2)
	{
		r = new Rectangle(min(p1.x, p2.x) , min(p1.y, p2.y), abs(p1.x - p2.x), abs(p1.y - p2.y));
	}
	public Rectangle get()
	{
		return (r);
	}
}