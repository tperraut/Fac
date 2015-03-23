abstract class Creature
{
	private Cell c;

	public Creature (Cell c)
	{
		c = c;
	}
	public void paintCreature (Graphics2D g2D, int leftX, int topY, int scale)
	{
		Ellispe2D elli= new Ellispe2D.Double(leftX, topY, scale, scale);
		g2d.setPaint(setColor());
		g2d.fill(rect);
	}
	public void move(Direction dir)
	{
	}
	public Color setColor()
	{
		return (Color.WHITE);
	}
}
