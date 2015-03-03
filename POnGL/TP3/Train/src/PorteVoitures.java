public class PorteVoitures extends EltTransporteur<Voiture>
{
	public PorteVoitures(int poids, int capacite)
	{
		super(poids, capacite);
	}
	public int calculerVolume() {
		int volumeTotal = 0;
		for (Voiture t : this.cargo)
			volumeTotal += t.getVolume();
		return (volumeTotal);
	}
	@Override
	public boolean ajouterTransportable(Voiture t) {
		if (this.calculerVolume() + t.getVolume() < this.capacite)
		{
			this.cargo.add(t);
			return (true);
		}
		return false;
	}
	public String toString(){
		return "PorteVoiture : poids total = " + getPoids() +
			", volume occupée/volume totale = " + this.calculerVolume() +
			"/" + capacite +
			", nombre de voiture = " + cargo.size();
	}
}
