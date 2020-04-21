import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import models.*;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class EstimateFeeTest {

    @BeforeEach
    void beforeEach() {
    }

    @Test
    void testNullDeliveryFreq() {
        // If no delivery frequency is defined, the fees should be zero
        Estimate estimate = new Estimate(100, false, null, null, null, new ArrayList<>(), new ArrayList<>());
        estimate.addFee(new DeliveryFee(0.1f, Frequency.HOLIDAY, false, estimate));
        assertEquals(estimate.getFees(), 0);
    }

    @Test
    void testMissingDeliveryFreq() {
        // If we don't have any fees defined for the set delivery frequency, fees should
        // be 0
        Estimate estimate = new Estimate(100, false, null, Frequency.WEEKEND, null, new ArrayList<>(),
                new ArrayList<>());
        estimate.addFee(new DeliveryFee(0.1f, Frequency.HOLIDAY, false, estimate));
        assertEquals(estimate.getFees(), 0);
    }

    @Test
    void testPositiveFlatFee() {
        // A positive flat fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(300, false, null, Frequency.DAILY, null, new ArrayList<>(), new ArrayList<>());
        estimate.addFee(new DeliveryFee(125f, Frequency.DAILY, true, estimate));
        estimate.addFee(new DeliveryFee(300f, Frequency.WEEKEND, true, estimate));
        assertEquals(estimate.getFees(), 125);
    }

    @Test
    void testNegativeFlatFee() {
        // A negative flat fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(231, false, null, Frequency.HOLIDAY, null, new ArrayList<>(),
                new ArrayList<>());
        estimate.addFee(new DeliveryFee(1000f, Frequency.EMERGENCY, true, estimate));
        estimate.addFee(new DeliveryFee(-28f, Frequency.HOLIDAY, true, estimate));
        assertEquals(estimate.getFees(), -28);
    }

    @Test
    void testZeroFlatFee() {
        // A zero flat fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(231, false, null, Frequency.WEEKDAY, null, new ArrayList<>(),
                new ArrayList<>());
        estimate.addFee(new DeliveryFee(0f, Frequency.WEEKDAY, true, estimate));
        estimate.addFee(new DeliveryFee(20f, Frequency.WEEKEND, true, estimate));
        estimate.addFee(new DeliveryFee(80f, Frequency.HOLIDAY, true, estimate));
        assertEquals(estimate.getFees(), 0);
    }

    @Test
    void testPositivePercentFee() {
        // A positive percent fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(300, false, null, Frequency.DAILY, null, new ArrayList<>(), new ArrayList<>());
        estimate.addFee(new DeliveryFee(0.25f, Frequency.DAILY, false, estimate));
        estimate.addFee(new DeliveryFee(0.3f, Frequency.WEEKEND, false, estimate));
        assertEquals(estimate.getFees(), 75);
    }

    @Test
    void testNegativePercentFee() {
        // A negative percent fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(250, false, null, Frequency.EMERGENCY, null, new ArrayList<>(),
                new ArrayList<>());
        estimate.addFee(new DeliveryFee(0.15f, Frequency.DAILY, false, estimate));
        estimate.addFee(new DeliveryFee(-0.2f, Frequency.EMERGENCY, false, estimate));
        estimate.addFee(new DeliveryFee(0.5f, Frequency.HOLIDAY, false, estimate));
        assertEquals(estimate.getFees(), -50);
    }

    @Test
    void testZeroPercentFee() {
        // A zero percent fee should be applied, based on the delivery frequency
        Estimate estimate = new Estimate(231, false, null, Frequency.DAILY, null, new ArrayList<>(), new ArrayList<>());
        estimate.addFee(new DeliveryFee(0f, Frequency.DAILY, false, estimate));
        estimate.addFee(new DeliveryFee(0.1f, Frequency.WEEKEND, false, estimate));
        estimate.addFee(new DeliveryFee(0.2f, Frequency.HOLIDAY, false, estimate));
        estimate.addFee(new DeliveryFee(0.3f, Frequency.EMERGENCY, false, estimate));
        assertEquals(estimate.getFees(), 0);
    }
}
