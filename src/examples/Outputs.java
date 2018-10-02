class Outputs {
    public int[] intOutputs;
    @Override

    public boolean equals(Object obj) {
        if (Outputs.class.isInstance(obj)) {
            Outputs o = (Outputs) obj;
            if (o.intOutputs.length != intOutputs.length) {
                System.out.println("length mismatch");
                return false;
            }
            for (int i=0; i < intOutputs.length; i++) {
                if (intOutputs[i] != o.intOutputs[i]) {
                    System.out.println("entry " + i + " mismatch, " + intOutputs[i] + ", " + o.intOutputs[i]);
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}