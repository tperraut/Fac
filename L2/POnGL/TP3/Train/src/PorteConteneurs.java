public class PorteConteneurs extends EltTransporteur<Conteneur>
{
	/**
	 * Constructeur de PorteConteneur.
	 * @param poids  donne le poids de l'élément à vide.
	 * @param capacite  donne le volume total de marchandises transportables.
	 */
	public PorteConteneurs(int poids, int capacite) {
		super(poids, capacite);
	}

	/**
	 * Calcul du volume total des éléments transportés.
	 */
	public int calculerVolume() {
		int volumeTotal = 0;
		for (Conteneur t : this.cargo)
			volumeTotal += t.getVolume();
		return (volumeTotal);
	}

	/**
	 * Redéfinition de la fonction d'ajout, pour tenir compte du
	 * volume des conteneurs.
	 */
	@Override
	public boolean ajouterTransportable(Conteneur t) {
		if (this.calculerVolume() + t.getVolume() < this.capacite)
		{
			this.cargo.add(t);
			return (true);
		}
		return false;
	}

	/**
	 * Produit un descriptif de l'élément.
	 */
	public String toString(){
		return "PorteConteneur : poids total = " + getPoids() +
			", capacité occupée/capacité totale = " + this.calculerVolume() +
			"/" + capacite;
	}
}
