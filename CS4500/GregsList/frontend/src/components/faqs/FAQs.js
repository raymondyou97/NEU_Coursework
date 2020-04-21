import React from 'react';
import FAQService from '../../services/FAQService';
import FAQRows from './FAQRows';
import { Button, ButtonGroup, Table, Container } from 'react-bootstrap';

class FAQs extends React.Component {
  constructor(props) {
    super(props);
    this.faqService = FAQService.getInstance();
    this.state = {
      faqs: [],
      newTitle: '',
      newQuestion: '',
      totalPages: '',
      currentPage: 0,
      perPage: 10,
      toggle: false,
    };
  }

  componentDidMount() {
    this.faqService
      .findAllFrequentlyAskedQuestions(
        this.state.currentPage,
        this.state.perPage,
        this.state.newTitle,
        this.state.newQuestion
      )
      .then(faqs => {
        this.setState({
          faqs: faqs.content,
          totalPages: faqs.totalPages,
        });
      });
  }

  handleTitleChange = e => {
    this.setState({ newTitle: e.target.value });
  };

  handleQuestionChange = e => {
    this.setState({ newQuestion: e.target.value });
  };

  createFAQ = () => {
    // Send a create request
    this.faqService
      .createFAQ({
        title: this.state.newTitle,
        question: this.state.newQuestion,
      })
      .then(() =>
        this.handleUpdateState(this.state.currentPage, this.state.perPage)
      );
  };

  pageButtons = () => {
    var buttons = [];
    for (var i = 0; i < this.state.totalPages; i++) {
      buttons.push(i);
    }
    return buttons;
  };

  handlePrevButton = () => {
    if (this.state.currentPage > 0) {
      this.handleUpdateState(this.state.currentPage - 1, this.state.perPage);
    }
  };

  handleNextButton = () => {
    if (this.state.currentPage < this.state.totalPages - 1) {
      this.handleUpdateState(this.state.currentPage + 1, this.state.perPage);
    }
  };

  handlePageUpdate = e => {
    this.handleUpdateState(Number(e.target.value), this.state.perPage);
  };

  handlePageCount = e => {
    if (e.target.value === 'All') {
      this.handleUpdateState(0, '');
    } else {
      this.handleUpdateState(0, Number(e.target.value));
    }
  };

  handleUpdateState = (newCurrPage, perPage) => {
    this.faqService
      .findAllFrequentlyAskedQuestions(
        newCurrPage,
        perPage,
        this.state.toggle ? this.state.newTitle : '',
        this.state.toggle ? this.state.newQuestion : ''
      )
      .then(faqs => {
        this.setState({
          currentPage: newCurrPage,
          totalPages: faqs.totalPages,
          perPage: perPage,
          faqs: faqs.content,
        });
      });
  };

  handleFilter = e => {
    this.setState(
      {
        toggle: !this.state.toggle,
      },
      () => {
        this.handleUpdateState(0, this.state.perPage);
      }
    );
  };

  handleUpdate = (id, data) => {
    this.faqService
      .updateFAQ(id, data)
      .then(() =>
        this.handleUpdateState(this.state.currentPage, this.state.perPage)
      );
  };

  handleDelete = id => {
    this.faqService
      .deleteFAQ(id)
      .then(() =>
        this.handleUpdateState(this.state.currentPage, this.state.perPage)
      );
  };

  render() {
    return (
      <Container>
        <h3>Frequently Asked Questions</h3>
        <div>
          <Table bordered striped>
            <thead>
              <tr>
                <th>Title</th>
                <th>Question</th>
                <th />
                <th />
              </tr>
              <tr>
                <td>
                  <input
                    type="text"
                    placeholder="Enter title"
                    value={this.state.newTitle}
                    onChange={this.handleTitleChange}
                  />
                </td>
                <td>
                  <input
                    type="text"
                    placeholder="Enter question"
                    value={this.state.newQuestion}
                    onChange={this.handleQuestionChange}
                  />
                </td>
                <td>
                  <Button
                    style={{ height: 'auto' }}
                    variant="secondary"
                    onClick={this.createFAQ}
                  >
                    +
                  </Button>
                </td>
                <td>
                  <Button
                    style={{ height: 'auto' }}
                    variant="secondary"
                    onClick={this.handleFilter}
                  >
                    Filter
                  </Button>
                </td>
              </tr>
            </thead>
            <tbody>
              <FAQRows
                faqs={this.state.faqs}
                onUpdate={this.handleUpdate}
                onDelete={this.handleDelete}
              />
            </tbody>
          </Table>
        </div>
        <ButtonGroup>
          <Button
            style={{ height: 'auto' }}
            variant="secondary"
            onClick={this.handlePrevButton}
            disabled={this.state.currentPage === 0}
          >
            Previous
          </Button>
          {this.pageButtons().map(button => (
            <Button
              style={{ height: 'auto' }}
              variant="secondary"
              key={button}
              value={button}
              onClick={this.handlePageUpdate}
            >
              {button + 1}
            </Button>
          ))}
          <Button
            style={{ height: 'auto' }}
            variant="secondary"
            onClick={this.handleNextButton}
            disabled={this.state.currentPage >= this.state.totalPages - 1}
          >
            Next
          </Button>
        </ButtonGroup>
        <div>
          <label>Items Per Page</label>
          <select name="pageCount" onChange={this.handlePageCount}>
            <option value="10">10</option>
            <option value="25">25</option>
            <option value="50">50</option>
            <option value="100">100</option>
            <option value="All">All</option>
          </select>
        </div>
      </Container>
    );
  }
}

export default FAQs;
