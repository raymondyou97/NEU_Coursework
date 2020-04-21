package models;

import com.fasterxml.jackson.annotation.JsonIgnore;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.Table;

@Entity
@Table(name = "subscription_discount")
public class SubscriptionDiscount {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private float discount;
    private Frequency frequency;
    private boolean flat;

    @ManyToOne
    @JsonIgnore
    private Estimate estimate;

    public SubscriptionDiscount() {
    }

    public SubscriptionDiscount(float discount, Frequency frequency, boolean flat, Estimate estimate) {
        this.discount = discount;
        this.frequency = frequency;
        this.flat = flat;
        this.estimate = estimate;
    }

    public void setDiscount(float discount) {
        this.discount = discount;
    }

    public float getDiscount() {
        return discount;
    }

    public void setFlat(boolean flat) {
        this.flat = flat;
    }

    public boolean isFlat() {
        return flat;
    }

    public Estimate getEstimate() {
        return estimate;
    }

    public void setEstimate(Estimate estimate) {
        this.estimate = estimate;
    }

    public Frequency getFrequency() {
        return this.frequency;
    }

    public float calculateDiscount(float estimate) {
        if (flat) {
            return -discount;
        } else {
            return -(estimate * discount);
        }
    }
}
