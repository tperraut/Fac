class Wall extends Cell
{
	public Wall(LModel laby, int i, int j)
	{
		this.busy = true;
		super(laby, i, j);
	}
	public Color setColor()
	{
		return (Color.BLACK);
	}
	public Creature setHM()
	{
		HM = new Nobody(this);
	}
}
