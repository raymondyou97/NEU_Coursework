package models;

import com.fasterxml.jackson.annotation.JsonIgnore;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.Table;

@Entity
@Table(name = "delivery_fee")
public class DeliveryFee {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private float fee;
    private Frequency frequency;
    private boolean flat;

    @ManyToOne
    @JsonIgnore
    private Estimate estimate;

    public DeliveryFee(float fee, Frequency frequency, boolean flat, Estimate estimate) {
        this.fee = fee;
        this.frequency = frequency;
        this.flat = flat;
        this.estimate = estimate;
    }

    public float getFee() {
        return fee;
    }

    public void setFee(float fee) {
        this.fee = fee;
    }

    public Frequency getFrequency() {
        return frequency;
    }

    public void setFrequency(Frequency frequency) {
        this.frequency = frequency;
    }

    public boolean isFlat() {
        return flat;
    }

    public void setFlat(boolean flat) {
        this.flat = flat;
    }

    public Estimate getEstimate() {
        return estimate;
    }

    public void setEstimate(Estimate estimate) {
        this.estimate = estimate;
    }

    public float calculateFee(float basePrice) {
        if (flat) {
            return fee;
        } else {
            return basePrice * fee;
        }
    }
}
