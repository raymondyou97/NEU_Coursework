package repositories;

import models.ServiceAnswer;
import org.springframework.data.jpa.repository.JpaRepository;

public interface PagedServiceAnswerRepository extends JpaRepository<ServiceAnswer, Integer> {

}
