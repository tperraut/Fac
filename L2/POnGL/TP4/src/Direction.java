/**
 * Directions cardinales, et équivalents en différences de coordonnées.
 */

enum Direction {
	NORTH (-1, 0),
	SOUTH ( 1, 0),
	EAST  ( 0, 1),
	WEST  ( 0,-1),
	CENTER( 0, 0);

	private final int dI, dJ;
	private Direction(int di, int dj) { this.dI = di; this.dJ = dj; }
	public int dI() { return dI; }
	public int dJ() { return dJ; }
	public Direction random() { return Direction.CENTER; }
}
