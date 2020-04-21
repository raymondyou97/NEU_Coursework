package models;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.OneToMany;
import javax.persistence.Table;

@Entity
@Table(name = "estimate")
public class Estimate {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private float basePrice;
    private boolean subscription;
    private Frequency subscriptionFrequency;
    private Frequency deliveryFrequency;
    private Frequency baseFrequency;
    @OneToMany(mappedBy = "estimate")
    private Map<Frequency, SubscriptionDiscount> discounts = new HashMap<>();
    @OneToMany(mappedBy = "estimate")
    private Map<Frequency, DeliveryFee> fees = new HashMap<>();
    @OneToMany(mappedBy = "estimate")
    private List<RewardDiscount> rewards;

    public Estimate() {
    }

    public Estimate(float basePrice, boolean subscription, Frequency subscriptionFrequency, Frequency deliveryFrequency,
            Frequency baseFrequency, List<SubscriptionDiscount> discounts, List<RewardDiscount> rewards) {
        this.basePrice = basePrice;
        this.subscription = subscription;
        this.subscriptionFrequency = subscriptionFrequency;
        this.deliveryFrequency = deliveryFrequency;
        this.baseFrequency = baseFrequency;

        for (SubscriptionDiscount discount : discounts) {
            this.discounts.put(discount.getFrequency(), discount);
        }

        this.rewards = rewards;
    }

    public void setBaseFrequency(Frequency baseFrequency) {
        this.baseFrequency = baseFrequency;
    }

    public void setBasePrice(float basePrice) {
        this.basePrice = basePrice;
    }

    public void setDeliveryFrequency(Frequency deliveryFrequency) {
        this.deliveryFrequency = deliveryFrequency;
    }

    public void setSubscription(boolean subscription) {
        this.subscription = subscription;
    }

    public void setSubscriptionFrequency(Frequency subscriptionFrequency) {
        this.subscriptionFrequency = subscriptionFrequency;
    }

    public void setDiscounts(List<SubscriptionDiscount> discounts) {
        this.discounts = new HashMap<>();
        for (SubscriptionDiscount discount : discounts) {
            this.discounts.put(discount.getFrequency(), discount);
        }
    }

    public void setRewards(List<RewardDiscount> rewards) {
        this.rewards = rewards;
    }

    public void addFee(DeliveryFee fee) {
        this.fees.put(fee.getFrequency(), fee);
    }

    public float getBasePrice() {
        return basePrice;
    }

    public boolean isSubscription() {
        return subscription;
    }

    public Frequency getBaseFrequency() {
        return baseFrequency;
    }

    public Frequency getDeliveryFrequency() {
        return deliveryFrequency;
    }

    public Frequency getSubscriptionFrequency() {
        return subscriptionFrequency;
    }

    public float getEstimate() {
        return this.basePrice + this.getDiscount() + this.getFees();
    }

    public float getDiscount() {
        // if it's not a subscription return rewards only
        if (!this.subscription) {
            float current_discount = 0f;
            for (RewardDiscount reward : rewards) {
                current_discount += reward.calculateDiscount(basePrice);
            }
            return current_discount;
        }

        // if the base frequency is a onetime, holiday,
        // or emergency return rewards only
        if (this.baseFrequency.equals(Frequency.ONETIME) || this.baseFrequency.equals(Frequency.HOLIDAY)
                || this.baseFrequency.equals(Frequency.EMERGENCY)) {
            float current_discount = 0f;
            for (RewardDiscount reward : rewards) {
                current_discount += reward.calculateDiscount(basePrice);
            }
            return current_discount;
        }

        // Convert down to hourly price based on base price and frequency
        float current_discount = 0f;
        SubscriptionDiscount subscription_discount = this.discounts.get(this.subscriptionFrequency);
        if (subscription_discount != null) {
            current_discount += subscription_discount.calculateDiscount(basePrice);
        }
        for (RewardDiscount reward : rewards) {
            current_discount += reward.calculateDiscount(basePrice);
        }

        return current_discount;
    }

    public float getFees() {
        // If a fee is defined for this delivery frequency, then apply it, otherwise the
        // fee is 0
        DeliveryFee fee = this.fees.get(this.deliveryFrequency);
        if (fee != null) {
            return fee.calculateFee(this.basePrice);
        }
        return 0;
    }
}
