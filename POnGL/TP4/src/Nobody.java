class Nobody extends Creature
{
	public void move(Direction dir){}
	public void paintCreature (Graphics2D g2D, int leftX, int topY, int scale)
	{
		c.paintCell(g2D, leftX, topY, scale);
	}
}
